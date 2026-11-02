import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7.Lifting

open scoped BigOperators Matrix

namespace SequenceIndependentLifting

section Theorem77

variable {n : ℕ}

/-- Helper for ch7_sec7_2_2_theorem_7_7: the cover-supported projection of a point, obtained by
zeroing every coordinate outside `C`. -/
def coverSupportedPoint
    (C : Finset (Fin n))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ if j ∈ C then x j else 0

/-- Helper for ch7_sec7_2_2_theorem_7_7: on the cover `C`, `coverSupportedPoint` agrees with the
original point. -/
@[simp] lemma coverSupportedPoint_apply_of_mem
    {C : Finset (Fin n)}
    {x : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∈ C) :
    coverSupportedPoint C x j = x j := by
  simp [coverSupportedPoint, hj]

/-- Helper for ch7_sec7_2_2_theorem_7_7: outside `C`, `coverSupportedPoint` vanishes. -/
@[simp] lemma coverSupportedPoint_apply_of_not_mem
    {C : Finset (Fin n)}
    {x : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ C) :
    coverSupportedPoint C x j = 0 := by
  simp [coverSupportedPoint, hj]

/-- Helper for ch7_sec7_2_2_theorem_7_7: the base inequality only sees the coordinates in `C`,
so projecting away off-cover coordinates does not change its dot product. -/
lemma baseCoefficients_dotProduct_coverSupportedPoint_eq
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (x : Fin n → ℝ) :
    base_coefficients C α ⬝ᵥ coverSupportedPoint C x =
      base_coefficients C α ⬝ᵥ x := by
  -- Compare the dot-product summands coordinatewise; outside `C` both base coefficients are `0`.
  rw [dotProduct, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hmem : j ∈ C
  · simp [hmem]
  · simp [hmem]

/-- Helper for ch7_sec7_2_2_theorem_7_7: the total knapsack weight splits into the weight on the
cover-supported projection plus the sum of the active off-cover weights. -/
lemma knapsackWeight_eq_coverSupportedPoint_weight_add_active
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (x : Fin n → ℝ)
    (hx_bin : ∀ j, x j = 0 ∨ x j = 1) :
    ∑ j : Fin n, a j * x j =
      ∑ j : Fin n, a j * coverSupportedPoint C x j +
        ((Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)).sum fun j => a j) := by
  -- Each coordinate contributes either through the cover projection or through the active
  -- off-cover set, according to whether it lies in `C` and whether `x j = 1`.
  calc
    ∑ j : Fin n, a j * x j
      = ∑ j : Fin n,
          (a j * coverSupportedPoint C x j +
            if j ∉ C ∧ x j = 1 then a j else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rcases hx_bin j with hxj | hxj
          · by_cases hmem : j ∈ C
            · simp [coverSupportedPoint, hmem, hxj]
            · simp [coverSupportedPoint, hmem, hxj]
          · by_cases hmem : j ∈ C
            · simp [coverSupportedPoint, hmem, hxj]
            · simp [coverSupportedPoint, hmem, hxj]
    _ = ∑ j : Fin n, a j * coverSupportedPoint C x j +
          ∑ j : Fin n, if j ∉ C ∧ x j = 1 then a j else 0 := by
          rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin n, a j * coverSupportedPoint C x j +
          (Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)).sum fun j => a j := by
          simp [Finset.sum_filter]

/-- Helper for ch7_sec7_2_2_theorem_7_7: rewriting the lifted dot product separates the base part
from the active off-cover contribution. -/
lemma liftedCoefficients_dotProduct_eq_base_plus_active
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (g : ℝ → ℝ)
    (x : Fin n → ℝ)
    (hx : x ∈ zero_one_knapsack_set a b) :
    lifted_coefficients C α a g ⬝ᵥ x =
      base_coefficients C α ⬝ᵥ x +
        ((Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)).sum fun j => g (a j)) := by
  rcases (mem_zero_one_knapsack_set_iff a b x).mp hx with ⟨hx_bin, _⟩
  -- Coordinatewise, the lifted coefficient contributes `g (a j)` exactly on the active
  -- off-cover coordinates, and otherwise matches the base coefficient.
  calc
    lifted_coefficients C α a g ⬝ᵥ x
      = ∑ j : Fin n,
          (base_coefficients C α j * x j +
            if j ∉ C ∧ x j = 1 then g (a j) else 0) := by
          rw [dotProduct]
          refine Finset.sum_congr rfl ?_
          intro j hj
          rcases hx_bin j with hxj | hxj
          · by_cases hmem : j ∈ C
            · simp [hmem, hxj]
            · simp [hmem, hxj]
          · by_cases hmem : j ∈ C
            · simp [hmem, hxj]
            · simp [hmem, hxj]
    _ = ∑ j : Fin n, base_coefficients C α j * x j +
          ∑ j : Fin n, if j ∉ C ∧ x j = 1 then g (a j) else 0 := by
          rw [Finset.sum_add_distrib]
    _ = base_coefficients C α ⬝ᵥ x +
          (Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)).sum fun j => g (a j) := by
          simp [dotProduct, Finset.sum_filter]

/-- Helper for ch7_sec7_2_2_theorem_7_7: a nonempty finite family of weights in `[0,b]` compresses
under superadditivity to the value at its total sum. -/
lemma superadditive_sum_le_of_nonempty
    (a : Fin n → ℝ)
    (g : ℝ → ℝ)
    (b : ℝ)
    (hg_super : is_superadditive_on_Icc g b)
    (J : Finset (Fin n))
    (hJ : J.Nonempty)
    (haJ : ∀ ⦃j : Fin n⦄, j ∈ J → a j ∈ Set.Icc (0 : ℝ) b)
    (hsum : J.sum a ∈ Set.Icc (0 : ℝ) b) :
    J.sum (fun j => g (a j)) ≤ g (J.sum a) := by
  classical
  -- Induct on the finite set, using superadditivity to append one weight at a time.
  revert hJ haJ hsum
  refine Finset.induction_on J ?_ ?_
  · intro hJ haJ hsum
    rcases hJ with ⟨w, hw⟩
    cases hw
  · intro j J hj ih hinsert haInsert hsumInsert
    by_cases hJ : J.Nonempty
    · have haj : a j ∈ Set.Icc (0 : ℝ) b := haInsert (by simp [hj])
      have htail_mem : J.sum a ∈ Set.Icc (0 : ℝ) b := by
        refine ⟨?_, ?_⟩
        · exact Finset.sum_nonneg fun k hk ↦ (haInsert (by simp [hk])).1
        · have hsum_le : a j + J.sum a ≤ b := by
            simpa [Finset.sum_insert, hj] using hsumInsert.2
          linarith [haj.1]
      have htail : J.sum (fun k => g (a k)) ≤ g (J.sum a) := by
        refine ih hJ ?_ htail_mem
        intro k hk
        exact haInsert (by simp [hk])
      -- Append the new weight using one application of superadditivity.
      calc
        (insert j J).sum (fun k => g (a k))
            = g (a j) + J.sum (fun k => g (a k)) := by simp [Finset.sum_insert, hj]
        _ ≤ g (a j) + g (J.sum a) := by gcongr
        _ ≤ g (a j + J.sum a) := by
              exact hg_super haj htail_mem (by simpa [Finset.sum_insert, hj] using hsumInsert)
        _ = g ((insert j J).sum a) := by simp [Finset.sum_insert, hj]
    · have hJ_empty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      -- The singleton case is the base of the nonempty induction.
      simp [hJ_empty]

/-- Helper for ch7_sec7_2_2_theorem_7_7: every knapsack point yields a residual weight `z ∈ [0,b]`
whose lifting-profile value controls the base part of the inequality. -/
lemma baseValue_add_liftingProfile_le_of_knapsackPoint
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (hC_nonneg : ∀ ⦃j : Fin n⦄, j ∈ C → 0 ≤ a j)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (x : Fin n → ℝ)
    (hx : x ∈ zero_one_knapsack_set a b) :
    let J := Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)
    let z := J.sum a
    z ∈ Set.Icc (0 : ℝ) b ∧
      base_coefficients C α ⬝ᵥ x + lifting_profile a b C α β z ≤ β := by
  classical
  rcases (mem_zero_one_knapsack_set_iff a b x).mp hx with ⟨hx_bin, hx_weight⟩
  let J : Finset (Fin n) := Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)
  let z : ℝ := J.sum a
  let xC : Fin n → ℝ := coverSupportedPoint C x
  have hweight_split :
      ∑ j : Fin n, a j * x j = ∑ j : Fin n, a j * xC j + z := by
    simpa [J, z, xC] using
      knapsackWeight_eq_coverSupportedPoint_weight_add_active a C x hx_bin
  have hz_nonneg : 0 ≤ z := by
    -- Every active off-cover weight lies in `[0,b]`, so this sum is nonnegative.
    refine Finset.sum_nonneg ?_
    intro j hj
    have hj_mem : j ∉ C ∧ x j = 1 := by
      simpa [J] using Finset.mem_filter.mp hj
    exact (ha hj_mem.1).1
  have hxC_weight_nonneg : 0 ≤ ∑ j : Fin n, a j * xC j := by
    -- The projected point keeps only cover coordinates, whose weights are assumed nonnegative.
    refine Finset.sum_nonneg ?_
    intro j hj
    by_cases hmem : j ∈ C
    · rcases hx_bin j with hxj | hxj
      · simp [xC, hmem, hxj]
      · simp [xC, hmem, hxj, hC_nonneg hmem]
    · simp [xC, hmem]
  have hz_le : z ≤ b := by
    linarith [hx_weight, hweight_split, hxC_weight_nonneg]
  have hz : z ∈ Set.Icc (0 : ℝ) b := ⟨hz_nonneg, hz_le⟩
  have hxC_mem_residual : xC ∈ zero_one_knapsack_set a (b - z) := by
    rw [mem_zero_one_knapsack_set_iff]
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hmem : j ∈ C
      · simpa [xC, hmem] using hx_bin j
      · left
        simp [xC, hmem]
    · linarith [hx_weight, hweight_split]
  have hxC_zero_off : ∀ j, j ∉ C → xC j = 0 := by
    intro j hj
    simp [xC, hj]
  have hprofile_set_bdd :
      BddAbove
        {r : ℝ |
          ∃ y : Fin n → ℝ,
            y ∈ zero_one_knapsack_set a (b - z) ∧
            (∀ j, j ∉ C → y j = 0) ∧
            r = base_coefficients C α ⬝ᵥ y} := by
    refine ⟨β, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy_mem, hy_zero, rfl⟩
    have hy_mem_b : y ∈ zero_one_knapsack_set a b := by
      rcases (mem_zero_one_knapsack_set_iff a (b - z) y).mp hy_mem with ⟨hy_bin, hy_weight⟩
      rw [mem_zero_one_knapsack_set_iff]
      exact ⟨hy_bin, by linarith [hy_weight, hz_nonneg]⟩
    exact hbase hy_mem_b
  have hbase_le_sup :
      base_coefficients C α ⬝ᵥ x ≤
        sSup
          {r : ℝ |
            ∃ y : Fin n → ℝ,
              y ∈ zero_one_knapsack_set a (b - z) ∧
              (∀ j, j ∉ C → y j = 0) ∧
              r = base_coefficients C α ⬝ᵥ y} := by
    -- The projected point is an admissible witness for the residual profile.
    have hwitness :
        base_coefficients C α ⬝ᵥ x ∈
          {r : ℝ |
            ∃ y : Fin n → ℝ,
              y ∈ zero_one_knapsack_set a (b - z) ∧
              (∀ j, j ∉ C → y j = 0) ∧
              r = base_coefficients C α ⬝ᵥ y} := by
      refine ⟨xC, hxC_mem_residual, hxC_zero_off, ?_⟩
      symm
      exact baseCoefficients_dotProduct_coverSupportedPoint_eq C α x
    exact le_csSup hprofile_set_bdd hwitness
  refine ⟨hz, ?_⟩
  -- Rewrite the profile and use the projected witness bound inside the supremum.
  dsimp [lifting_profile]
  linarith

/-- Helper for ch7_sec7_2_2_theorem_7_7: updating a cover-supported residual witness at one
off-cover coordinate adds exactly that coordinate's coefficient to the dot product. -/
lemma updatedCoverSupportedPoint_dotProduct
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    {c' : Fin n → ℝ}
    (hc' : is_lifting_of_base_inequality (zero_one_knapsack_set a b) C α β c')
    {j : Fin n}
    (hj : j ∉ C)
    {x : Fin n → ℝ}
    (hx_zero : ∀ k, k ∉ C → x k = 0) :
    c' ⬝ᵥ Function.update x j 1 =
      base_coefficients C α ⬝ᵥ x + c' j := by
  -- Compare the updated dot product coordinatewise; outside `C`, the residual witness already
  -- vanishes, and on `C` the lifting agrees with the base coefficients.
  rw [dotProduct, dotProduct]
  calc
    ∑ k : Fin n, c' k * Function.update x j 1 k
      = ∑ k : Fin n,
          (base_coefficients C α k * x k + if k = j then c' j else 0) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          by_cases hkj : k = j
          · subst k
            simp [hj, hx_zero j hj]
          · by_cases hmem : k ∈ C
            · simp [hkj, hmem, hc'.2 hmem]
            · simp [hkj, hmem, hx_zero k hmem]
    _ = ∑ k : Fin n, base_coefficients C α k * x k +
          ∑ k : Fin n, if k = j then c' j else 0 := by
            rw [Finset.sum_add_distrib]
    _ = base_coefficients C α ⬝ᵥ x + c' j := by
          simp [dotProduct]

/-- Helper for ch7_sec7_2_2_theorem_7_7: updating a cover-supported residual witness at one
off-cover coordinate adds exactly the corresponding weight to the knapsack sum. -/
lemma updatedCoverSupportedPoint_weight
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    {j : Fin n}
    (hj : j ∉ C)
    {x : Fin n → ℝ}
    (hx_zero : ∀ k, k ∉ C → x k = 0) :
    ∑ k : Fin n, a k * Function.update x j 1 k =
      ∑ k : Fin n, a k * x k + a j := by
  -- The updated point changes only coordinate `j`, and the residual witness already has `x j = 0`.
  calc
    ∑ k : Fin n, a k * Function.update x j 1 k
      = ∑ k : Fin n, (a k * x k + if k = j then a j else 0) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          by_cases hkj : k = j
          · subst k
            simp [hx_zero j hj]
          · simp [hkj]
    _ = ∑ k : Fin n, a k * x k + ∑ k : Fin n, if k = j then a j else 0 := by
          rw [Finset.sum_add_distrib]
    _ = ∑ k : Fin n, a k * x k + a j := by simp

/-- Helper for ch7_sec7_2_2_theorem_7_7: every lifting coefficient outside `C` is bounded above
by the sequence-independent lifting profile at the corresponding weight. -/
lemma liftingCoeff_le_liftingProfile_of_lifting
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    {c' : Fin n → ℝ}
    (hc' : is_lifting_of_base_inequality (zero_one_knapsack_set a b) C α β c')
    {j : Fin n}
    (hj : j ∉ C) :
    c' j ≤ lifting_profile a b C α β (a j) := by
  classical
  have haj : a j ∈ Set.Icc (0 : ℝ) b := ha hj
  let S : Set ℝ :=
    {r : ℝ |
      ∃ x : Fin n → ℝ,
        x ∈ zero_one_knapsack_set a (b - a j) ∧
        (∀ k, k ∉ C → x k = 0) ∧
        r = base_coefficients C α ⬝ᵥ x}
  have hS_nonempty : S.Nonempty := by
    -- The zero vector is always a residual witness for `z = a j`.
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [mem_zero_one_knapsack_set_iff]
      refine ⟨?_, ?_⟩
      · intro k
        left
        simp
      · simp
        linarith [haj.2]
    · intro k hk
      simp
    · simp [dotProduct]
  have hS_le : ∀ r ∈ S, r ≤ β - c' j := by
    intro r hr
    rcases hr with ⟨x, hx_mem, hx_zero, rfl⟩
    let y : Fin n → ℝ := Function.update x j 1
    have hy_mem : y ∈ zero_one_knapsack_set a b := by
      rcases (mem_zero_one_knapsack_set_iff a (b - a j) x).mp hx_mem with ⟨hx_bin, hx_weight⟩
      rw [mem_zero_one_knapsack_set_iff]
      refine ⟨?_, ?_⟩
      · intro k
        by_cases hkj : k = j
        · right
          subst hkj
          simp [y]
        · simpa [y, hkj] using hx_bin k
      · -- The update adds exactly the missing weight `a j`.
        simpa [y] using
          (updatedCoverSupportedPoint_weight a C hj hx_zero).trans_le (by linarith [hx_weight])
    have hy_valid : c' ⬝ᵥ y ≤ β := hc'.1 hy_mem
    have hy_dot :
        c' ⬝ᵥ y = base_coefficients C α ⬝ᵥ x + c' j := by
      simpa [y] using updatedCoverSupportedPoint_dotProduct a b C α β hc' hj hx_zero
    linarith
  have hsup : sSup S ≤ β - c' j := csSup_le hS_nonempty hS_le
  -- Unfold the profile and rearrange the supremum bound.
  dsimp [lifting_profile, S]
  linarith

/-- Theorem 7.7. Every superadditive function `g` on `[0,b]` that is pointwise bounded above by
the lifting profile yields a valid lifted inequality when the cover weights are nonnegative
and the off-cover coefficients are evaluated at weights in `[0,b]`. -/
theorem superadditive_lift_valid
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (g : ℝ → ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (hC_nonneg : ∀ ⦃j : Fin n⦄, j ∈ C → 0 ≤ a j)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hg_super : is_superadditive_on_Icc g b)
    (hg_le :
      ∀ ⦃z : ℝ⦄, z ∈ Set.Icc (0 : ℝ) b → g z ≤ lifting_profile a b C α β z) :
    is_valid_inequality
      (zero_one_knapsack_set a b)
      (lifted_coefficients C α a g)
      β := by
  -- Route correction: prove validity directly from the `lifting_profile` supremum rather than
  -- recreating the source proof's intermediate family `f_i`.
  rw [is_valid_inequality_iff]
  intro x hx
  let J : Finset (Fin n) := Finset.univ.filter (fun j ↦ j ∉ C ∧ x j = 1)
  let z : ℝ := J.sum a
  have hx_base :
      z ∈ Set.Icc (0 : ℝ) b ∧
        base_coefficients C α ⬝ᵥ x + lifting_profile a b C α β z ≤ β := by
    simpa [J, z] using
      baseValue_add_liftingProfile_le_of_knapsackPoint a b C α β hbase hC_nonneg ha x hx
  have hz : z ∈ Set.Icc (0 : ℝ) b := hx_base.1
  have hbase_profile : base_coefficients C α ⬝ᵥ x + lifting_profile a b C α β z ≤ β := hx_base.2
  have hlifted :
      lifted_coefficients C α a g ⬝ᵥ x =
        base_coefficients C α ⬝ᵥ x + J.sum (fun j => g (a j)) := by
    simpa [J] using liftedCoefficients_dotProduct_eq_base_plus_active a b C α g x hx
  by_cases hJ : J.Nonempty
  · -- Compress the active off-cover contribution to a single profile argument `z`.
    have hsum_g :
        J.sum (fun j => g (a j)) ≤ g z := by
      refine superadditive_sum_le_of_nonempty a g b hg_super J hJ ?_ ?_
      · intro j hj
        have hj_mem : j ∉ C ∧ x j = 1 := by
          simpa [J] using Finset.mem_filter.mp hj
        exact ha hj_mem.1
      · simpa [z]
          using hz
    calc
      lifted_coefficients C α a g ⬝ᵥ x
          = base_coefficients C α ⬝ᵥ x + J.sum (fun j => g (a j)) := hlifted
      _ ≤ base_coefficients C α ⬝ᵥ x + g z := by gcongr
      _ ≤ base_coefficients C α ⬝ᵥ x + lifting_profile a b C α β z := by
            gcongr
            exact hg_le hz
      _ ≤ β := hbase_profile
  · -- If no off-cover coordinate is active, the lifted inequality is the base inequality.
    have hJ_empty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    calc
      lifted_coefficients C α a g ⬝ᵥ x
          = base_coefficients C α ⬝ᵥ x + 0 := by simp [hlifted, hJ_empty]
      _ = base_coefficients C α ⬝ᵥ x := by ring
      _ ≤ β := hbase hx

/-- Consequence for Theorem 7.7: if the lifting profile itself is superadditive on `[0,b]`,
then the lifted inequality obtained from that profile is the unique maximal lifting of the
base inequality on the binary knapsack set, provided the cover weights are nonnegative
and the off-cover weights lie in `[0,b]`. -/
theorem lifting_profile_is_unique_maximal_lifting
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hbase :
      is_valid_inequality (zero_one_knapsack_set a b) (base_coefficients C α) β)
    (hC_nonneg : ∀ ⦃j : Fin n⦄, j ∈ C → 0 ≤ a j)
    (ha : ∀ ⦃j : Fin n⦄, j ∉ C → a j ∈ Set.Icc (0 : ℝ) b)
    (hf_super : is_superadditive_on_Icc (lifting_profile a b C α β) b) :
    is_unique_maximal_lifting_of_base_inequality
      (zero_one_knapsack_set a b)
      C
      α
      β
      (lifted_coefficients C α a (lifting_profile a b C α β)) := by
  -- First prove the profile itself is a lifting, then show every other lifting lies below it.
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact
        superadditive_lift_valid a b C α β (lifting_profile a b C α β)
          hbase hC_nonneg ha hf_super (fun {_} _ ↦ le_rfl)
    · intro j hj
      simp [hj]
  · intro c' hc' j
    by_cases hj : j ∈ C
    · rw [hc'.2 hj]
      simp [hj]
    · simpa [hj] using liftingCoeff_le_liftingProfile_of_lifting a b C α β ha hc' hj

end Theorem77

end SequenceIndependentLifting
