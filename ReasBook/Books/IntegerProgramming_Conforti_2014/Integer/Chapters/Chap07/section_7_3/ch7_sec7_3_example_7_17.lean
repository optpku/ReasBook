import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_16

open scoped BigOperators
open OrderedFlowCover

-- Declarations for this item will be appended below by the statement pipeline.

section Example717

/-- The capacity vector `(17, 9, 8, 6, 5, 4)` from Example 7.17. -/
def example_7_17_capacity : Fin 6 → ℝ
  | 0 => 17
  | 1 => 9
  | 2 => 8
  | 3 => 6
  | 4 => 5
  | 5 => 4

/-- The right-hand side `20` from Example 7.17. -/
def example_7_17_rhs : ℝ :=
  20

/-- The flow-cover set `C = {3,4,5,6}` from Example 7.17, written with zero-based `Fin 6`
indices as `{2,3,4,5}`. -/
def example_7_17_cover : Finset (Fin 6) :=
  {2, 3, 4, 5}

/-- The source cover in Example 7.17 has four elements. -/
theorem example_7_17_cover_card :
    example_7_17_cover.card = 4 := by
  decide

/-- The cover excess `λ = 23 - 20 = 3` for Example 7.17. -/
def example_7_17_excess : ℝ :=
  3

/-- The flow-cover excess attached to `example_7_17_cover` is the source value `3`. -/
theorem example_7_17_excess_eq_flow_cover_excess :
    example_7_17_excess =
      flow_cover_excess example_7_17_capacity example_7_17_rhs example_7_17_cover := by
  -- Expand the concrete cover sum and compute the source excess directly.
  have hsum : ∑ j ∈ example_7_17_cover, example_7_17_capacity j = 23 := by
    simp [example_7_17_cover, example_7_17_capacity]
    norm_num
  rw [flow_cover_excess_eq_sum_sub]
  rw [hsum]
  norm_num [example_7_17_excess, example_7_17_rhs]

/-- The capacities in Example 7.17 are nonnegative. -/
theorem example_7_17_capacity_nonneg (i : Fin 6) :
    0 ≤ example_7_17_capacity i := by
  fin_cases i <;> norm_num [example_7_17_capacity]

/-- The source cover `C = {3,4,5,6}` is a flow cover for Example 7.17. -/
instance example_7_17_isFlowCover :
    IsFlowCover example_7_17_capacity example_7_17_rhs example_7_17_cover := by
  -- The cover capacities sum to `23`, so the explicit cover is valid.
  rw [isFlowCover_iff]
  have hsum : ∑ j ∈ example_7_17_cover, example_7_17_capacity j = 23 := by
    simp [example_7_17_cover, example_7_17_capacity]
    norm_num
  rw [hsum, example_7_17_rhs]
  norm_num

/-- The right-hand side `9` of the lifted flow cover inequality in Example 7.17. -/
def example_7_17_inequality_rhs : ℝ :=
  9

/-- The single-node flow set
`T = {(x,y) ∈ {0,1}^6 × ℝ^6_+ | y₁ + ⋯ + y₆ ≤ 20, y₁ ≤ 17 x₁, y₂ ≤ 9 x₂, y₃ ≤ 8 x₃,
y₄ ≤ 6 x₄, y₅ ≤ 5 x₅, y₆ ≤ 4 x₆}` from Example 7.17, encoded in `((Fin 6 → ℝ) × (Fin 6 → ℝ))`.
-/
def example_7_17_flow_set : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  single_node_flow_set example_7_17_capacity example_7_17_rhs

/-- Membership in `example_7_17_flow_set` is exactly the explicit binary, nonnegativity,
capacity, and upper-bound system from Example 7.17. -/
theorem mem_example_7_17_flow_set_iff
    {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} :
    p ∈ example_7_17_flow_set ↔
      (∀ i, p.1 i = 0 ∨ p.1 i = 1) ∧
        (∀ i, 0 ≤ p.2 i) ∧
          p.2 0 + p.2 1 + p.2 2 + p.2 3 + p.2 4 + p.2 5 ≤ 20 ∧
            p.2 0 ≤ 17 * p.1 0 ∧
              p.2 1 ≤ 9 * p.1 1 ∧
                p.2 2 ≤ 8 * p.1 2 ∧
                  p.2 3 ≤ 6 * p.1 3 ∧
                    p.2 4 ≤ 5 * p.1 4 ∧
                      p.2 5 ≤ 4 * p.1 5 := by
  constructor
  · intro hp
    rcases (mem_single_node_flow_set_iff example_7_17_capacity example_7_17_rhs p).1 hp with
      ⟨hx, hy, hsum, hcap⟩
    refine ⟨hx, hy, ?_, hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5⟩
    simpa [example_7_17_rhs, Fin.sum_univ_six] using hsum
  · intro hp
    rcases hp with ⟨hx, hy, hsum, h0, h1, h2, h3, h4, h5⟩
    refine (mem_single_node_flow_set_iff example_7_17_capacity example_7_17_rhs p).2 ?_
    refine ⟨hx, hy, ?_, ?_⟩
    · simpa [example_7_17_rhs, Fin.sum_univ_six] using hsum
    · intro i
      fin_cases i
      · simpa [example_7_17_capacity] using h0
      · simpa [example_7_17_capacity] using h1
      · simpa [example_7_17_capacity] using h2
      · simpa [example_7_17_capacity] using h3
      · simpa [example_7_17_capacity] using h4
      · simpa [example_7_17_capacity] using h5

/-- The admissible lifting pairs `(α₁, β₁)` for the coordinates `(y₁, x₁)` in Example 7.17. -/
def example_7_17_first_lifting_pairs : Set (ℝ × ℝ) :=
  {p |
    p = (0, 0) ∨
      p = ((1 / 2 : ℝ), (-(5 / 2 : ℝ))) ∨
        p = ((3 / 5 : ℝ), (-(18 / 5 : ℝ))) ∨
          p = (1, -10)}

/-- Membership in `example_7_17_first_lifting_pairs` means belonging to the four listed
possibilities for `(α₁, β₁)`. -/
theorem mem_example_7_17_first_lifting_pairs_iff
    {p : ℝ × ℝ} :
    p ∈ example_7_17_first_lifting_pairs ↔
      p = (0, 0) ∨
        p = ((1 / 2 : ℝ), (-(5 / 2 : ℝ))) ∨
          p = ((3 / 5 : ℝ), (-(18 / 5 : ℝ))) ∨
            p = (1, -10) := Iff.rfl

/-- The admissible lifting pairs `(α₂, β₂)` for the coordinates `(y₂, x₂)` in Example 7.17. -/
def example_7_17_second_lifting_pairs : Set (ℝ × ℝ) :=
  {p | p = (0, 0) ∨ p = ((3 / 4 : ℝ), (-(15 / 4 : ℝ)))}

/-- Membership in `example_7_17_second_lifting_pairs` means belonging to the two listed
possibilities for `(α₂, β₂)`. -/
theorem mem_example_7_17_second_lifting_pairs_iff
    {p : ℝ × ℝ} :
    p ∈ example_7_17_second_lifting_pairs ↔
      p = (0, 0) ∨ p = ((3 / 4 : ℝ), (-(15 / 4 : ℝ))) := Iff.rfl

/-- The ordered cover data from Theorem 7.16 specialized to Example 7.17 lists the cover indices
`2, 3, 4, 5`, corresponding to the source indices `3, 4, 5, 6`. -/
def example_7_17_cover_order : Fin example_7_17_cover.card ↪ Fin 6 :=
  { toFun := fun i ↦ ⟨i.1 + 2, by
      have hi : i.1 < 4 := by
        simpa [example_7_17_cover_card] using i.2
      omega⟩
    inj' := by
      intro i j hij
      apply Fin.ext
      exact Nat.add_right_cancel (Fin.ext_iff.mp hij) }

/-- The ordered cover data for Example 7.17 enumerates `example_7_17_cover`. -/
theorem example_7_17_cover_order_enumerates :
    enumerates example_7_17_cover example_7_17_cover_order := by
  -- Compare the range of the four-entry order with the concrete cover, one index at a time.
  rw [enumerates]
  apply Set.Subset.antisymm
  · rintro i ⟨h, rfl⟩
    fin_cases h <;>
      norm_num [example_7_17_cover, example_7_17_cover_order, Fin.ext_iff]
  · intro i hi
    have hcard0 : 0 < example_7_17_cover.card := by
      simp [example_7_17_cover_card]
    have hcard1 : 1 < example_7_17_cover.card := by
      simp [example_7_17_cover_card]
    have hcard2 : 2 < example_7_17_cover.card := by
      simp [example_7_17_cover_card]
    have hcard3 : 3 < example_7_17_cover.card := by
      simp [example_7_17_cover_card]
    let h0 : Fin example_7_17_cover.card := ⟨0, hcard0⟩
    let h1 : Fin example_7_17_cover.card := ⟨1, hcard1⟩
    let h2 : Fin example_7_17_cover.card := ⟨2, hcard2⟩
    let h3 : Fin example_7_17_cover.card := ⟨3, hcard3⟩
    fin_cases i
    · simp [example_7_17_cover] at hi
    · simp [example_7_17_cover] at hi
    · have hvalue : example_7_17_cover_order h0 = 2 := by
        apply Fin.ext
        norm_num [example_7_17_cover_order, h0]
      exact ⟨h0, hvalue⟩
    · have hvalue : example_7_17_cover_order h1 = 3 := by
        apply Fin.ext
        norm_num [example_7_17_cover_order, h1]
      exact ⟨h1, hvalue⟩
    · have hvalue : example_7_17_cover_order h2 = 4 := by
        apply Fin.ext
        norm_num [example_7_17_cover_order, h2]
      exact ⟨h2, hvalue⟩
    · have hvalue : example_7_17_cover_order h3 = 5 := by
        apply Fin.ext
        norm_num [example_7_17_cover_order, h3]
      exact ⟨h3, hvalue⟩

/-- Along the ordered cover of Example 7.17, the cover capacities are weakly decreasing. -/
theorem example_7_17_cover_order_antitone :
    Antitone fun h : Fin example_7_17_cover.card ↦
      example_7_17_capacity (example_7_17_cover_order h) := by
  -- Exhaust the four ordered cover positions and compare the explicit values `8, 6, 5, 4`.
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals
    first
      | exact False.elim (by simpa using hij)
      | norm_num [example_7_17_capacity, example_7_17_cover_order]

/-- The cut index `r` from Theorem 7.16 is `4` in Example 7.17. -/
def example_7_17_cutIndex : ℕ :=
  4

/-- The Example 7.17 cut index satisfies the source cut-index conditions from Theorem 7.16. -/
theorem example_7_17_cutIndex_isCutIndex :
    isCutIndex
      example_7_17_capacity
      example_7_17_cover
      example_7_17_cover_order
      example_7_17_excess
      example_7_17_cutIndex := by
  -- Unfold the source cut-index conditions at the explicit values `r = 4` and `λ = 3`.
  refine ⟨by norm_num [example_7_17_cutIndex], by norm_num [example_7_17_cutIndex, example_7_17_cover_card], ?_, ?_⟩
  · -- The fourth ordered coefficient is `4`, which is still strictly above `λ = 3`.
    norm_num [example_7_17_cutIndex, example_7_17_excess, weight, example_7_17_cover_card,
      example_7_17_cover_order, example_7_17_capacity]
  · -- There is no ordered position strictly after `r = 4` inside the four-element cover.
    intro h hr_lt hh_le
    exact False.elim <|
      (Nat.not_lt_of_ge (by simpa [example_7_17_cutIndex, example_7_17_cover_card] using hh_le)) hr_lt

/-- Helper for Example 7.17: the ordered cover coefficients are exactly `8, 6, 5, 4`. -/
theorem example_7_17_weight_values :
    weight example_7_17_cover example_7_17_capacity example_7_17_cover_order 1 = 8 ∧
      weight example_7_17_cover example_7_17_capacity example_7_17_cover_order 2 = 6 ∧
        weight example_7_17_cover example_7_17_capacity example_7_17_cover_order 3 = 5 ∧
          weight example_7_17_cover example_7_17_capacity example_7_17_cover_order 4 = 4 := by
  -- Evaluate the four ordered-cover coefficients once so later proofs can reuse the constants.
  norm_num [weight, example_7_17_cover_card, example_7_17_cover_order, example_7_17_capacity]

/-- Helper for Example 7.17: the ordered cover partial sums are `0, 8, 14, 19, 23`. -/
theorem example_7_17_partialSum_values :
    partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 0 = 0 ∧
      partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 1 = 8 ∧
        partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 2 = 14 ∧
          partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 3 = 19 ∧
            partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 4 = 23 := by
  -- Expand the recursive definition once on the concrete Example 7.17 ordered cover.
  norm_num [partialSum, weight, example_7_17_cover_card, example_7_17_cover_order,
    example_7_17_capacity]

/-- The listed admissible pairs for `(α₁, β₁)` are exactly the Theorem 7.16 admissible pairs for
the first noncover coordinate. -/
theorem example_7_17_first_lifting_pair_iff_admissiblePair
    (α₁ β₁ : ℝ) :
    (α₁, β₁) ∈ example_7_17_first_lifting_pairs ↔
      admissiblePair
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        example_7_17_cover_order
        example_7_17_cutIndex
        0
        α₁
        β₁ := by
  -- Normalize the excess first, leaving only the three finite families in `admissiblePair`.
  rw [mem_example_7_17_first_lifting_pairs_iff]
  unfold admissiblePair
  rw [← example_7_17_excess_eq_flow_cover_excess]
  constructor
  · rintro (hzero | hsecond | hthird | hfourth)
    · injection hzero with hα hβ
      subst α₁
      subst β₁
      exact Or.inl ⟨rfl, rfl⟩
    · injection hsecond with hα hβ
      subst α₁
      subst β₁
      have hhLower : 2 ≤ (2 : ℕ) := by
        norm_num
      have hhUpper : 2 ≤ example_7_17_cutIndex := by
        norm_num [example_7_17_cutIndex]
      refine Or.inr <| Or.inl ⟨2, hhLower, hhUpper, ?_, ?_, ?_⟩
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
    · injection hthird with hα hβ
      subst α₁
      subst β₁
      have hhLower : 2 ≤ (3 : ℕ) := by
        norm_num
      have hhUpper : 3 ≤ example_7_17_cutIndex := by
        norm_num [example_7_17_cutIndex]
      refine Or.inr <| Or.inl ⟨3, hhLower, hhUpper, ?_, ?_, ?_⟩
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
    · injection hfourth with hα hβ
      subst α₁
      subst β₁
      have hcapacity :
          example_7_17_capacity 0 >
            partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 3 -
              example_7_17_excess := by
        norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      have hℓUpper : 3 < example_7_17_cutIndex := by
        norm_num [example_7_17_cutIndex]
      have hcapacityUpper :
          example_7_17_capacity 0 ≤
            partialSum example_7_17_cover example_7_17_capacity example_7_17_cover_order 3 := by
        norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      refine Or.inr <| Or.inr <| Or.inl ⟨3, hcapacity, Or.inr ⟨hℓUpper, hcapacityUpper⟩, rfl, ?_⟩
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
  · rintro (hzero | hCover | hTerminal | hGap)
    · rcases hzero with ⟨hα, hβ⟩
      subst α₁
      subst β₁
      exact Or.inl rfl
    · rcases hCover with ⟨h, hhLower, hhUpper, hcapacity, hα, hβ⟩
      norm_num [example_7_17_cutIndex] at hhUpper
      have hh : h = 2 ∨ h = 3 ∨ h = 4 := by
        omega
      rcases hh with rfl | rfl | rfl
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hα hβ
        subst α₁
        subst β₁
        exact Or.inr <| Or.inl rfl
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hα hβ
        subst α₁
        subst β₁
        exact Or.inr <| Or.inr <| Or.inl rfl
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacity
    · rcases hTerminal with ⟨ℓ, hcapacity, hposition, hα, hβ⟩
      rcases hposition with rfl | ⟨hℓUpper, hcapacityUpper⟩
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cutIndex,
          example_7_17_cover_card, example_7_17_cover_order, example_7_17_capacity] at hcapacity
      · norm_num [example_7_17_cutIndex] at hℓUpper
        have hℓ : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 := by
          omega
        rcases hℓ with rfl | rfl | rfl | rfl
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hβ
          subst α₁
          subst β₁
          exact Or.inr <| Or.inr <| Or.inr rfl
    · rcases hGap with ⟨ℓ, hℓUpper, hcapacityLower, hcapacityUpper, hα, hβ⟩
      norm_num [example_7_17_cutIndex] at hℓUpper
      have hℓ : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 := by
        omega
      rcases hℓ with rfl | rfl | rfl | rfl
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityLower

/-- The listed admissible pairs for `(α₂, β₂)` are exactly the Theorem 7.16 admissible pairs for
the second noncover coordinate. -/
theorem example_7_17_second_lifting_pair_iff_admissiblePair
    (α₂ β₂ : ℝ) :
    (α₂, β₂) ∈ example_7_17_second_lifting_pairs ↔
      admissiblePair
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        example_7_17_cover_order
        example_7_17_cutIndex
        1
        α₂
        β₂ := by
  -- Normalize the excess and enumerate the bounded cover positions in the three source families.
  rw [mem_example_7_17_second_lifting_pairs_iff]
  unfold admissiblePair
  rw [← example_7_17_excess_eq_flow_cover_excess]
  constructor
  · rintro (hzero | hnonzero)
    · injection hzero with hα hβ
      subst α₂
      subst β₂
      exact Or.inl ⟨rfl, rfl⟩
    · injection hnonzero with hα hβ
      subst α₂
      subst β₂
      have hℓUpper : 1 < example_7_17_cutIndex := by
        norm_num [example_7_17_cutIndex]
      refine Or.inr <| Or.inr <| Or.inr ⟨1, hℓUpper, ?_, ?_, ?_, ?_⟩
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity]
  · rintro (hzero | hCover | hTerminal | hGap)
    · rcases hzero with ⟨hα, hβ⟩
      subst α₂
      subst β₂
      exact Or.inl rfl
    · rcases hCover with ⟨h, hhLower, hhUpper, hcapacity, hα, hβ⟩
      norm_num [example_7_17_cutIndex] at hhUpper
      have hh : h = 2 ∨ h = 3 ∨ h = 4 := by
        omega
      rcases hh with rfl | rfl | rfl <;>
        norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacity
    · rcases hTerminal with ⟨ℓ, hcapacity, hposition, hα, hβ⟩
      rcases hposition with rfl | ⟨hℓUpper, hcapacityUpper⟩
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cutIndex,
          example_7_17_cover_card, example_7_17_cover_order, example_7_17_capacity] at hcapacity
      · norm_num [example_7_17_cutIndex] at hℓUpper
        have hℓ : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 := by
          omega
        rcases hℓ with rfl | rfl | rfl | rfl
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacity
        · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
            example_7_17_cover_order, example_7_17_capacity] at hcapacity
    · rcases hGap with ⟨ℓ, hℓUpper, hcapacityLower, hcapacityUpper, hα, hβ⟩
      norm_num [example_7_17_cutIndex] at hℓUpper
      have hℓ : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 := by
        omega
      rcases hℓ with rfl | rfl | rfl | rfl
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityUpper
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hα hβ
        subst α₂
        subst β₂
        exact Or.inr rfl
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityLower
      · norm_num [partialSum, weight, example_7_17_excess, example_7_17_cover_card,
          example_7_17_cover_order, example_7_17_capacity] at hcapacityLower

/-- The `α`-coefficients on `N \ C = {1,2}` from Example 7.17, written with zero-based
`Fin 6` indices as `{0,1}`. -/
def example_7_17_alpha_coeffs (α₁ α₂ : ℝ) : Fin 6 → ℝ
  | 0 => α₁
  | 1 => α₂
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

/-- The `β`-coefficients on `N \ C = {1,2}` from Example 7.17, written with zero-based
`Fin 6` indices as `{0,1}`. -/
def example_7_17_beta_coeffs (β₁ β₂ : ℝ) : Fin 6 → ℝ
  | 0 => β₁
  | 1 => β₂
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

/-- The left-hand side of the lifted flow cover inequality from Example 7.17 evaluated at a point
`(x, y)` and coefficient pair choices `(α₁, β₁)` and `(α₂, β₂)`. -/
def example_7_17_lifted_flow_cover_value
    (α₁ β₁ α₂ β₂ : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) : ℝ :=
  α₁ * p.2 0 + β₁ * p.1 0 + α₂ * p.2 1 + β₂ * p.1 1 +
    p.2 2 + p.2 3 + p.2 4 + p.2 5 - 5 * p.1 2 - 3 * p.1 3 - 2 * p.1 4 - p.1 5

/-- `example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p` expands to the explicit left-hand side
of the lifted flow cover inequality from Example 7.17. -/
theorem example_7_17_lifted_flow_cover_value_eq
    (α₁ β₁ α₂ β₂ : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) :
    example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p =
      α₁ * p.2 0 + β₁ * p.1 0 + α₂ * p.2 1 + β₂ * p.1 1 +
        p.2 2 + p.2 3 + p.2 4 + p.2 5 - 5 * p.1 2 - 3 * p.1 3 - 2 * p.1 4 - p.1 5 :=
  rfl

/-- The canonical lifted flow-cover owner from Theorem 7.16 differs from the source-facing
left-hand side in Example 7.17 by the constant shift `20 - 9 = 11`. -/
theorem flow_cover_lifted_value_eq_example_7_17_lifted_flow_cover_value_add
    (α₁ β₁ α₂ β₂ : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) :
    flow_cover_lifted_value
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        p =
      example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p +
        (example_7_17_rhs - example_7_17_inequality_rhs) := by
  have hcomplement : Finset.univ \ example_7_17_cover = ({0, 1} : Finset (Fin 6)) := by
    -- The only noncover indices are the first two coordinates.
    ext i
    fin_cases i <;> simp [example_7_17_cover]
  -- Expand the canonical cover value and outside sum, then normalize the resulting polynomial.
  rw [flow_cover_lifted_value_eq, hcomplement]
  simp [flow_cover_value, flow_cover_excess, example_7_17_cover,
    example_7_17_capacity, example_7_17_rhs, example_7_17_inequality_rhs,
    example_7_17_alpha_coeffs, example_7_17_beta_coeffs,
    example_7_17_lifted_flow_cover_value]
  norm_num
  ring

/-- The equality face cut out on `conv(T)` by the lifted flow cover inequality from Example 7.17.
-/
def example_7_17_lifted_flow_cover_face
    (α₁ β₁ α₂ β₂ : ℝ) : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  {p |
    p ∈ convexHull ℝ example_7_17_flow_set ∧
      example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p = example_7_17_inequality_rhs}

/-- Membership in `example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂` means lying in `conv(T)` and
meeting the lifted flow cover inequality at equality. -/
theorem mem_example_7_17_lifted_flow_cover_face_iff
    {α₁ β₁ α₂ β₂ : ℝ}
    {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} :
    p ∈ example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂ ↔
      p ∈ convexHull ℝ example_7_17_flow_set ∧
        example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p = 9 := Iff.rfl

/-- The source-facing equality face from Example 7.17 coincides with the canonical face from
Theorem 7.16 after shifting the constant term to the right-hand side. -/
theorem example_7_17_lifted_flow_cover_face_iff_flow_cover_lifted_face
    (α₁ β₁ α₂ β₂ : ℝ)
    {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} :
    p ∈ example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂ ↔
      p ∈ flow_cover_lifted_face
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        example_7_17_rhs := by
  constructor
  · rintro ⟨hp, hEq⟩
    -- Rewrite the source-facing equality as the canonical equality with right-hand side `20`.
    refine ⟨by simpa [example_7_17_flow_set] using hp, ?_⟩
    rw [flow_cover_lifted_value_eq_example_7_17_lifted_flow_cover_value_add]
    linarith [hEq]
  · rintro ⟨hp, hEq⟩
    -- Move the constant shift back to recover the source-facing equality at right-hand side `9`.
    refine ⟨by simpa [example_7_17_flow_set] using hp, ?_⟩
    rw [flow_cover_lifted_value_eq_example_7_17_lifted_flow_cover_value_add] at hEq
    linarith [hEq]

/-- The lifted flow cover inequality from Example 7.17 is facet-defining for `conv(T)` when it is
valid on `conv(T)` and the equality face it cuts out is a facet of `conv(T)`. -/
def example_7_17_lifted_flow_cover_facet_defining
    (α₁ β₁ α₂ β₂ : ℝ) : Prop :=
  (∀ ⦃p : (Fin 6 → ℝ) × (Fin 6 → ℝ)⦄,
      p ∈ convexHull ℝ example_7_17_flow_set →
        example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p ≤ example_7_17_inequality_rhs) ∧
    IsFacetOf
      (convexHull ℝ example_7_17_flow_set)
      (example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂)

/-- `example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂` unfolds to validity of the
lifted flow cover inequality on `conv(T)` together with facetness of its equality face. -/
theorem example_7_17_lifted_flow_cover_facet_defining_iff
    {α₁ β₁ α₂ β₂ : ℝ} :
    example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂ ↔
      (∀ ⦃p : (Fin 6 → ℝ) × (Fin 6 → ℝ)⦄,
          p ∈ convexHull ℝ example_7_17_flow_set →
            example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p ≤ 9) ∧
        IsFacetOf
          (convexHull ℝ example_7_17_flow_set)
          (example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂) := Iff.rfl

/-- The source-facing facet-defining predicate in Example 7.17 is equivalent to the canonical
Theorem 7.16 facet-defining owner after moving the constant `11` to the right-hand side. -/
theorem
    example_7_17_lifted_flow_cover_facet_defining_iff_flow_cover_lifted_inequality_facet_defining
    (α₁ β₁ α₂ β₂ : ℝ) :
    example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂ ↔
      flow_cover_lifted_inequality_facet_defining
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        example_7_17_rhs := by
  have hfaceEq :
      example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂ =
        flow_cover_lifted_face
          example_7_17_capacity
          example_7_17_rhs
          example_7_17_cover
          (example_7_17_alpha_coeffs α₁ α₂)
          (example_7_17_beta_coeffs β₁ β₂)
          example_7_17_rhs := by
    -- The two equality faces differ only by the constant-shift normalization.
    ext p
    exact example_7_17_lifted_flow_cover_face_iff_flow_cover_lifted_face α₁ β₁ α₂ β₂
  constructor
  · rintro ⟨hvalid, hfacet⟩
    -- Transport both the validity inequality and the equality face to the canonical owner.
    refine ⟨?_, ?_⟩
    · intro p hp
      have hpValid : example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p ≤ example_7_17_inequality_rhs :=
        hvalid (by simpa [example_7_17_flow_set] using hp)
      rw [flow_cover_lifted_value_eq_example_7_17_lifted_flow_cover_value_add]
      linarith [hpValid]
    · simpa [example_7_17_flow_set, hfaceEq] using hfacet
  · rintro ⟨hvalid, hfacet⟩
    -- Transport the canonical owner back to the source-facing inequality with right-hand side `9`.
    refine ⟨?_, ?_⟩
    · intro p hp
      have hpValid :
          flow_cover_lifted_value
              example_7_17_capacity
              example_7_17_rhs
              example_7_17_cover
              (example_7_17_alpha_coeffs α₁ α₂)
              (example_7_17_beta_coeffs β₁ β₂)
              p ≤ example_7_17_rhs :=
        hvalid (by simpa [example_7_17_flow_set] using hp)
      rw [flow_cover_lifted_value_eq_example_7_17_lifted_flow_cover_value_add] at hpValid
      linarith [hpValid]
    · simpa [example_7_17_flow_set, hfaceEq] using hfacet

/-- Helper for Example 7.17: an index lies outside `C = {2,3,4,5}` exactly when it is `0` or
`1`. -/
theorem example_7_17_not_mem_cover_iff (i : Fin 6) :
    i ∉ example_7_17_cover ↔ i = 0 ∨ i = 1 := by
  -- Exhaust the six possible indices against the explicit cover.
  fin_cases i <;> decide

/-- Example 7.17 restated through Theorem 7.16: the source lifting-pair lists are equivalent to
the canonical admissible-pair condition on the two coordinates outside the cover. -/
theorem example_7_17_all_outside_pairs_admissible_iff
    (α₁ β₁ α₂ β₂ : ℝ) :
    ((α₁, β₁) ∈ example_7_17_first_lifting_pairs ∧
        (α₂, β₂) ∈ example_7_17_second_lifting_pairs) ↔
      ∀ i, i ∉ example_7_17_cover →
        admissiblePair
          example_7_17_capacity
          example_7_17_rhs
          example_7_17_cover
          example_7_17_cover_order
          example_7_17_cutIndex
          i
          (example_7_17_alpha_coeffs α₁ α₂ i)
          (example_7_17_beta_coeffs β₁ β₂ i) := by
  constructor
  · rintro ⟨hFirst, hSecond⟩ i hi
    -- The only indices outside the cover are `0` and `1`, so rewrite with the two
    -- one-coordinate pair classifications.
    rcases (example_7_17_not_mem_cover_iff i).1 hi with rfl | rfl
    · simpa [example_7_17_alpha_coeffs, example_7_17_beta_coeffs] using
        (example_7_17_first_lifting_pair_iff_admissiblePair α₁ β₁).1 hFirst
    · simpa [example_7_17_alpha_coeffs, example_7_17_beta_coeffs] using
        (example_7_17_second_lifting_pair_iff_admissiblePair α₂ β₂).1 hSecond
  · intro hall
    -- Read the universal outside-index criterion at `i = 0` and `i = 1`.
    constructor
    · exact
        (example_7_17_first_lifting_pair_iff_admissiblePair α₁ β₁).2
          (by
            have hOutside : (0 : Fin 6) ∉ example_7_17_cover := by
              simp [example_7_17_cover]
            simpa [example_7_17_alpha_coeffs, example_7_17_beta_coeffs] using hall 0 hOutside)
    · exact
        (example_7_17_second_lifting_pair_iff_admissiblePair α₂ β₂).2
          (by
            have hOutside : (1 : Fin 6) ∉ example_7_17_cover := by
              simp [example_7_17_cover]
            simpa [example_7_17_alpha_coeffs, example_7_17_beta_coeffs] using hall 1 hOutside)

/-- Helper for Example 7.17: the explicit lifted functional is additive. -/
theorem example_7_17_lifted_flow_cover_value_add
    (α₁ β₁ α₂ β₂ : ℝ)
    (p q : (Fin 6 → ℝ) × (Fin 6 → ℝ)) :
    example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ (p + q) =
      example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p +
        example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ q := by
  -- Expand coordinatewise addition and collect the two copies of the functional.
  simp [example_7_17_lifted_flow_cover_value]
  ring

/-- Helper for Example 7.17: the explicit lifted functional commutes with scalar multiplication. -/
theorem example_7_17_lifted_flow_cover_value_smul
    (α₁ β₁ α₂ β₂ t : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) :
    example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ (t • p) =
      t * example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p := by
  -- Push the scalar through all twelve coordinates and factor it from the result.
  simp [example_7_17_lifted_flow_cover_value]
  ring

/-- Helper for Example 7.17: the explicit lifted left-hand side is a linear functional. -/
def example_7_17_liftedFlowCoverLinearMap
    (α₁ β₁ α₂ β₂ : ℝ) :
    ((Fin 6 → ℝ) × (Fin 6 → ℝ)) →ₗ[ℝ] ℝ :=
  { toFun := example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂
    map_add' := example_7_17_lifted_flow_cover_value_add α₁ β₁ α₂ β₂
    map_smul' := example_7_17_lifted_flow_cover_value_smul α₁ β₁ α₂ β₂ }

/-- Helper for Example 7.17: the cover contribution plus the common lifting profile at the
outside flow is bounded by the single-node right-hand side. -/
theorem example_7_17_cover_value_add_profile_le
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ))
    (hp : p ∈ example_7_17_flow_set) :
    flow_cover_value
          example_7_17_capacity example_7_17_rhs example_7_17_cover p +
        flow_cover_lifting_function
          example_7_17_rhs
          example_7_17_excess
          (example_7_17_capacity ∘ example_7_17_cover_order)
          (p.2 0 + p.2 1) ≤
      example_7_17_rhs := by
  classical
  rcases (mem_example_7_17_flow_set_iff.mp hp) with
    ⟨hx, hy, hsum, hcap0, hcap1, hcap2, hcap3, hcap4, hcap5⟩
  let x : Fin example_7_17_cover.card → Bool :=
    fun i ↦ decide (p.1 (example_7_17_cover_order i) = 1)
  let y : Fin example_7_17_cover.card → ℝ :=
    fun i ↦ p.2 (example_7_17_cover_order i)
  have hx_real (i : Fin example_7_17_cover.card) :
      (if x i then (1 : ℝ) else 0) = p.1 (example_7_17_cover_order i) := by
    rcases hx (example_7_17_cover_order i) with hzero | hone
    · simp [x, hzero]
    · simp [x, hone]
  have hmap : Finset.univ.map example_7_17_cover_order = example_7_17_cover := by
    -- The enumerating embedding identifies the finite universal set with the concrete cover.
    apply Finset.ext
    intro j
    rw [Finset.mem_map]
    simp only [Finset.mem_univ, true_and]
    change j ∈ Set.range example_7_17_cover_order ↔ j ∈ (example_7_17_cover : Set (Fin 6))
    rw [example_7_17_cover_order_enumerates]
  have hsum_reindex (F : Fin 6 → ℝ) :
      (∑ i, F (example_7_17_cover_order i)) = ∑ j ∈ example_7_17_cover, F j := by
    calc
      (∑ i, F (example_7_17_cover_order i)) =
          ∑ j ∈ Finset.univ.map example_7_17_cover_order, F j := by
            rw [Finset.sum_map]
      _ = ∑ j ∈ example_7_17_cover, F j :=
        congrArg (fun s : Finset (Fin 6) ↦ ∑ j ∈ s, F j) hmap
  have hobjective :
      flow_cover_value
          example_7_17_capacity example_7_17_rhs example_7_17_cover p ∈
        flow_cover_lifting_objective_values
          example_7_17_rhs
          example_7_17_excess
          (example_7_17_capacity ∘ example_7_17_cover_order)
          (p.2 0 + p.2 1) := by
    refine (mem_flow_cover_lifting_objective_values_iff _ _ _ _ _).2
      ⟨x, y, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hy (example_7_17_cover_order i)
    · -- Reindex the four cover flows and use the global flow bound.
      have hy_sum :
          ∑ i, y i = p.2 2 + p.2 3 + p.2 4 + p.2 5 := by
        rw [show (∑ i, y i) = ∑ i, p.2 (example_7_17_cover_order i) by rfl,
          hsum_reindex]
        simp [example_7_17_cover, add_assoc]
      rw [hy_sum]
      norm_num [example_7_17_rhs]
      linarith
    · intro i
      have hcap := (mem_single_node_flow_set_iff
        example_7_17_capacity example_7_17_rhs p).1 hp |>.2.2.2
      simpa [y, Function.comp_apply, hx_real i] using hcap (example_7_17_cover_order i)
    · -- The objective is precisely the canonical cover value after reindexing its four terms.
      rw [flow_cover_value_eq]
      rw [← example_7_17_excess_eq_flow_cover_excess]
      simp_rw [hx_real]
      rw [← Finset.sum_add_distrib]
      exact (hsum_reindex (fun j ↦
        p.2 j + max (example_7_17_capacity j - example_7_17_excess) 0 *
          (1 - p.1 j))).symm
  have hsup :
      flow_cover_value
          example_7_17_capacity example_7_17_rhs example_7_17_cover p ≤
        sSup
          (flow_cover_lifting_objective_values
            example_7_17_rhs
            example_7_17_excess
            (example_7_17_capacity ∘ example_7_17_cover_order)
            (p.2 0 + p.2 1)) :=
    le_csSup (by
      -- Every feasible objective is bounded by its residual demand plus all four penalties.
      refine ⟨(example_7_17_rhs - (p.2 0 + p.2 1)) +
        ∑ i, max
          ((example_7_17_capacity ∘ example_7_17_cover_order) i -
            example_7_17_excess) 0, ?_⟩
      intro v hv
      rcases (mem_flow_cover_lifting_objective_values_iff _ _ _ _ _).1 hv with
        ⟨x', y', hy'_nonneg, hy'_sum, hy'_cap, hv_eq⟩
      have hpenalty :
          (∑ i, max
              ((example_7_17_capacity ∘ example_7_17_cover_order) i -
                example_7_17_excess) 0 *
                (1 - if x' i then (1 : ℝ) else 0)) ≤
            ∑ i, max
              ((example_7_17_capacity ∘ example_7_17_cover_order) i -
                example_7_17_excess) 0 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        cases hxi : x' i <;> simp [hxi]
      rw [hv_eq, Finset.sum_add_distrib]
      linarith)
      hobjective
  -- Unfolding the profile turns the supremum comparison into the desired residual bound.
  unfold flow_cover_lifting_function
  linarith

/-- Helper for Example 7.17: the canonical lifted facet owner is equivalent to membership in the
two explicit lists of lifting pairs. -/
theorem example_7_17_flow_cover_lifted_inequality_facet_defining_iff_pairLists
    (α₁ β₁ α₂ β₂ : ℝ) :
    flow_cover_lifted_inequality_facet_defining
      example_7_17_capacity
      example_7_17_rhs
      example_7_17_cover
      (example_7_17_alpha_coeffs α₁ α₂)
      (example_7_17_beta_coeffs β₁ β₂)
      example_7_17_rhs ↔
        ((α₁, β₁) ∈ example_7_17_first_lifting_pairs ∧
          (α₂, β₂) ∈ example_7_17_second_lifting_pairs) := by
  -- Route correction: specialize the restored Theorem 7.16 classification instead of rebuilding
  -- its global facet geometry through a local two-coordinate release argument.
  have hcutIndex :
      isCutIndex
        example_7_17_capacity
        example_7_17_cover
        example_7_17_cover_order
        (flow_cover_excess
          example_7_17_capacity example_7_17_rhs example_7_17_cover)
        example_7_17_cutIndex := by
    rw [← example_7_17_excess_eq_flow_cover_excess]
    exact example_7_17_cutIndex_isCutIndex
  -- The generic outside-index condition is exactly the two concrete pair-list conditions.
  calc
    flow_cover_lifted_inequality_facet_defining
          example_7_17_capacity
          example_7_17_rhs
          example_7_17_cover
          (example_7_17_alpha_coeffs α₁ α₂)
          (example_7_17_beta_coeffs β₁ β₂)
          example_7_17_rhs ↔
        ∀ i, i ∉ example_7_17_cover →
          admissiblePair
            example_7_17_capacity
            example_7_17_rhs
            example_7_17_cover
            example_7_17_cover_order
            example_7_17_cutIndex
            i
            (example_7_17_alpha_coeffs α₁ α₂ i)
            (example_7_17_beta_coeffs β₁ β₂ i) :=
      flow_cover_inequality_facet_defining_iff_all_outside_pairs_admissible
        example_7_17_capacity
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        example_7_17_rhs
        example_7_17_cover
        example_7_17_cover_order
        example_7_17_cutIndex
        example_7_17_capacity_nonneg
        inferInstance
        example_7_17_cover_order_enumerates
        example_7_17_cover_order_antitone
        hcutIndex
    _ ↔
        ((α₁, β₁) ∈ example_7_17_first_lifting_pairs ∧
          (α₂, β₂) ∈ example_7_17_second_lifting_pairs) :=
      (example_7_17_all_outside_pairs_admissible_iff α₁ β₁ α₂ β₂).symm

/-- Helper for Example 7.17: the canonical lifted facet owner is equivalent to admissibility of
the two outside lifting pairs. -/
theorem
    example_7_17_flow_cover_lifted_inequality_facet_defining_iff_all_outside_pairs_admissible
    (α₁ β₁ α₂ β₂ : ℝ) :
    flow_cover_lifted_inequality_facet_defining
      example_7_17_capacity
      example_7_17_rhs
      example_7_17_cover
      (example_7_17_alpha_coeffs α₁ α₂)
      (example_7_17_beta_coeffs β₁ β₂)
      example_7_17_rhs ↔
        ∀ i, i ∉ example_7_17_cover →
          admissiblePair
            example_7_17_capacity
            example_7_17_rhs
            example_7_17_cover
            example_7_17_cover_order
            example_7_17_cutIndex
            i
            (example_7_17_alpha_coeffs α₁ α₂ i)
            (example_7_17_beta_coeffs β₁ β₂ i) := by
  -- Rewrite the geometric classification through the already-proved finite pair normalization.
  rw [example_7_17_flow_cover_lifted_inequality_facet_defining_iff_pairLists]
  exact example_7_17_all_outside_pairs_admissible_iff α₁ β₁ α₂ β₂

/-- Example 7.17. For the single-node flow set
`T = {(x,y) ∈ {0,1}^6 × ℝ^6_+ | y₁ + ⋯ + y₆ ≤ 20, y₁ ≤ 17 x₁, y₂ ≤ 9 x₂, y₃ ≤ 8 x₃,
y₄ ≤ 6 x₄, y₅ ≤ 5 x₅, y₆ ≤ 4 x₆}` and the flow cover `C = {3,4,5,6}`, the lifted flow cover
inequality
`α₁ y₁ + β₁ x₁ + α₂ y₂ + β₂ x₂ + y₃ + y₄ + y₅ + y₆ - 5 x₃ - 3 x₄ - 2 x₅ - x₆ ≤ 9`
is facet-defining for `conv(T)` if and only if `(α₁, β₁)` and `(α₂, β₂)` belong to the listed
sets of admissible lifting pairs. -/
theorem example_7_17_lifted_flow_cover_inequality_facet_defining_iff
    (α₁ β₁ α₂ β₂ : ℝ) :
    example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂ ↔
      (α₁, β₁) ∈ example_7_17_first_lifting_pairs ∧
        (α₂, β₂) ∈ example_7_17_second_lifting_pairs := by
  -- The source-facing statement is the canonical owner followed by the outside-index
  -- admissibility classification already proved above.
  rw [example_7_17_lifted_flow_cover_facet_defining_iff_flow_cover_lifted_inequality_facet_defining]
  rw [example_7_17_flow_cover_lifted_inequality_facet_defining_iff_all_outside_pairs_admissible]
  exact (example_7_17_all_outside_pairs_admissible_iff α₁ β₁ α₂ β₂).symm

end Example717
