/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_knapsack_cover
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_proposition_7_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_1_remark_7_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38.FacetTransport

open scoped BigOperators

section Theorem74

variable {n : ℕ}

/-- The prefix cover `{1, ..., t}` from Theorem 7.4, represented on `Fin n` by the indices
`< t`. -/
def theorem_7_4_cover
    (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i < t

/-- Membership in `theorem_7_4_cover t` means that the index lies among the first `t`
positions. -/
@[simp] theorem theorem_7_4_cover_mem_iff
    {t : ℕ}
    {j : Fin n} :
    j ∈ theorem_7_4_cover t ↔ j < t := by
  simp [theorem_7_4_cover]

/-- The ordered cover weights `a₁, ..., a_t` from Theorem 7.4, reindexed as a function on
`Fin t`. -/
def theorem_7_4_cover_weight
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Fin t → ℕ :=
  fun i ↦ weights (i.castLE ht)

/-- Evaluating `theorem_7_4_cover_weight weights ht` at `i` recovers the corresponding cover
weight from the first `t` indices. -/
@[simp] theorem theorem_7_4_cover_weight_apply
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n)
    (i : Fin t) :
    theorem_7_4_cover_weight weights ht i = weights (i.castLE ht) :=
  rfl

/-- `theorem_7_4_cover_weights_descending weights ht` records the assumption
`a₁ ≥ a₂ ≥ ··· ≥ a_t` from Theorem 7.4 on the ordered cover indices. -/
def theorem_7_4_cover_weights_descending
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Prop :=
  Antitone (theorem_7_4_cover_weight weights ht)

/-- Expanding `theorem_7_4_cover_weights_descending weights ht` recovers that the ordered cover
weights are antitone. -/
theorem theorem_7_4_cover_weights_descending_iff
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) :
    theorem_7_4_cover_weights_descending weights ht ↔
      Antitone (theorem_7_4_cover_weight weights ht) :=
  Iff.rfl

/-- The partial sums `μ_h = ∑_{ℓ=1}^h a_ℓ` from Theorem 7.4, extended to all natural indices by
summing the first `h` ordered cover weights among the first `t` positions. -/
def theorem_7_4_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) : ℕ → ℕ :=
  fun h ↦
    (Finset.range h).sum fun ℓ ↦
      if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0

/-- The initial partial sum from Theorem 7.4 is `μ₀ = 0`. -/
theorem theorem_7_4_mu_zero
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) :
    theorem_7_4_mu weights t ht 0 = 0 := by
  -- The initial partial sum is the empty sum over `range 0`.
  simp [theorem_7_4_mu]

/-- For `h < t`, the next partial sum from Theorem 7.4 satisfies `μ_{h+1} = μ_h + a_{h+1}` in
zero-based `Fin` indexing. -/
theorem theorem_7_4_mu_succ_of_lt
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (h : ℕ)
    (hh : h < t) :
    theorem_7_4_mu weights t ht (h + 1) =
      theorem_7_4_mu weights t ht h + theorem_7_4_cover_weight weights ht ⟨h, hh⟩ := by
  -- Split the next partial sum at the new index `h`.
  rw [theorem_7_4_mu, theorem_7_4_mu, Finset.sum_range_succ]
  -- The new summand is exactly the `h`th cover weight because `h < t`.
  simp [theorem_7_4_cover_weight, hh]

/-- The cover excess `λ = μ_t - b` from Theorem 7.4. -/
def theorem_7_4_cover_excess
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n) : ℕ :=
  theorem_7_4_mu weights t ht t - capacity

/-- Expanding `theorem_7_4_cover_excess weights capacity t ht` recovers the formula
`λ = μ_t - b` from Theorem 7.4. -/
theorem theorem_7_4_cover_excess_eq
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n) :
    theorem_7_4_cover_excess weights capacity t ht =
      theorem_7_4_mu weights t ht t - capacity :=
  rfl

/-- Helper for Theorem 7.4: the prefix cover `{i | i < t}` is exactly the image of `Fin t` in
`Fin n` under `Fin.castLE ht`. -/
theorem theorem_7_4_cover_eq_castLEImage
    (t : ℕ)
    (ht : t ≤ n) :
    theorem_7_4_cover (n := n) t =
      (Finset.univ : Finset (Fin t)).map
        (Fin.castLEEmb ht) := by
  ext j
  constructor
  · intro hj
    rw [Finset.mem_map]
    let i : Fin t := ⟨j, theorem_7_4_cover_mem_iff.mp hj⟩
    have hi : i ∈ (Finset.univ : Finset (Fin t)) := Finset.mem_univ i
    refine ⟨i, hi, ?_⟩
    exact Fin.ext rfl
  · intro hj
    rw [Finset.mem_map] at hj
    rcases hj with ⟨i, -, hij⟩
    subst hij
    simp [theorem_7_4_cover]

/-- Helper for Theorem 7.4: summing the weights over the prefix cover gives the partial sum
`μ_t`. -/
theorem theorem_7_4_cover_sum_eq_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) :
    (theorem_7_4_cover t).sum weights = theorem_7_4_mu weights t ht t := by
  let g : ℕ → ℕ := fun ℓ ↦
    if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0
  -- Reindex the prefix cover by the canonical embedding `Fin t ↪ Fin n`.
  rw [theorem_7_4_cover_eq_castLEImage (n := n) t ht]
  rw [Finset.sum_map]
  calc
    ∑ x : Fin t, weights (x.castLE ht)
      = ∑ x : Fin t, g x := by
          apply Finset.sum_congr rfl
          intro x hx
          dsimp [g]
          have hxcast : x.castLE ht = ⟨↑x, Nat.lt_of_lt_of_le x.isLt ht⟩ := by
            exact Fin.ext rfl
          rw [hxcast]
          simp [x.isLt]
    _ = ∑ ℓ ∈ Finset.range t, g ℓ := by
          simpa using (Fin.sum_univ_eq_sum_range g t)
    _ = theorem_7_4_mu weights t ht t := by
          simp [g, theorem_7_4_mu]

/-- Helper for Theorem 7.4: evaluating `μ_s` inside a larger prefix problem agrees with
evaluating the same prefix sum in the shorter prefix problem. -/
theorem theorem_7_4_mu_prefix_eq
    (weights : Fin n → ℕ)
    {s t : ℕ}
    (hsn : s ≤ n)
    (htn : t ≤ n)
    (hst : s ≤ t) :
    theorem_7_4_mu weights s hsn s = theorem_7_4_mu weights t htn s := by
  -- Every summand in `range s` lies below both cutoffs `s` and `t`.
  unfold theorem_7_4_mu
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hlt_s : ℓ < s := Finset.mem_range.mp hℓ
  have hlt_t : ℓ < t := Nat.lt_of_lt_of_le hlt_s hst
  simp [hlt_s, hlt_t]

/-- Helper for Theorem 7.4: minimality of the prefix cover implies `λ ≤ a_r` for every cover
index `r < t`. -/
theorem theorem_7_4_coverExcess_le_coverWeight
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (r : Fin t) :
    theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_cover_weight weights ht r := by
  have hrmem : r.castLE ht ∈ theorem_7_4_cover t := by
    simp [theorem_7_4_cover, r.isLt]
  have herase := hC.erase_sum_le (r.castLE ht) hrmem
  have hsum : (theorem_7_4_cover t).sum weights = theorem_7_4_mu weights t ht t :=
    theorem_7_4_cover_sum_eq_mu weights t ht
  -- Delete the cover item `r` and compare the remaining weight with the capacity.
  have hsum_le : (theorem_7_4_cover t).sum weights ≤ capacity + weights (r.castLE ht) := by
    have haux := Nat.add_le_add_right herase (weights (r.castLE ht))
    simpa [← (theorem_7_4_cover t).sum_erase_add weights hrmem,
      add_comm, add_left_comm, add_assoc] using haux
  have hmu_le : theorem_7_4_mu weights t ht t ≤ capacity + weights (r.castLE ht) := by
    simpa [hsum] using hsum_le
  have htarget : theorem_7_4_mu weights t ht t - capacity ≤ weights (r.castLE ht) := by
    omega
  simpa [theorem_7_4_cover_excess, theorem_7_4_cover_weight] using htarget

/-- The closed interval from Theorem 7.4 (1) is
`μ_h ≤ a_j ≤ μ_{h+1} - λ` for an index `j ∉ C`. -/
def theorem_7_4_exact_interval_condition
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) : Prop :=
  theorem_7_4_mu weights t ht h ≤ weights j ∧
    weights j ≤ theorem_7_4_mu weights t ht (h + 1) -
      theorem_7_4_cover_excess weights capacity t ht

/-- Expanding `theorem_7_4_exact_interval_condition weights capacity t ht j h` recovers the
closed interval condition `μ_h ≤ a_j ≤ μ_{h+1} - λ` from Theorem 7.4 (1). -/
theorem theorem_7_4_exact_interval_condition_iff
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) :
    theorem_7_4_exact_interval_condition weights capacity t ht j h ↔
      theorem_7_4_mu weights t ht h ≤ weights j ∧
        weights j ≤ theorem_7_4_mu weights t ht (h + 1) -
          theorem_7_4_cover_excess weights capacity t ht :=
  Iff.rfl

/-- The boundary interval from Theorem 7.4 is the open interval
`μ_{h+1} - λ < a_j < μ_{h+1}` for an index `j ∉ C`. -/
def theorem_7_4_boundary_interval_condition
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) : Prop :=
  theorem_7_4_mu weights t ht (h + 1) -
      theorem_7_4_cover_excess weights capacity t ht <
    weights j ∧
    weights j < theorem_7_4_mu weights t ht (h + 1)

/-- Expanding `theorem_7_4_boundary_interval_condition weights capacity t ht j h` recovers the
open interval condition `μ_{h+1} - λ < a_j < μ_{h+1}` from Theorem 7.4. -/
theorem theorem_7_4_boundary_interval_condition_iff
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (j : Fin n)
    (h : ℕ) :
    theorem_7_4_boundary_interval_condition weights capacity t ht j h ↔
    theorem_7_4_mu weights t ht (h + 1) -
          theorem_7_4_cover_excess weights capacity t ht <
        weights j ∧
        weights j < theorem_7_4_mu weights t ht (h + 1) :=
  Iff.rfl

/-- The facet-defining liftings of the prefix minimal cover from Theorem 7.4, expressed as valid
liftings of the cover inequality whose lifted face is a facet of the knapsack polytope. -/
abbrev theorem_7_4_facet_defining_liftings
    (weights : Fin n → ℕ)
    (capacity t : ℕ) :
    Set (Fin n → ℝ) :=
  facet_defining_liftings_of_minimal_cover_inequality
    weights
    capacity
    (theorem_7_4_cover t)

/-- Helper for Theorem 7.4: a shorter prefix cover is contained in a longer one. -/
theorem theorem_7_4_cover_subset
    {s t : ℕ}
    (hst : s ≤ t) :
    theorem_7_4_cover (n := n) s ⊆ theorem_7_4_cover t := by
  -- Membership is just the corresponding strict inequality on indices.
  intro i hi
  exact theorem_7_4_cover_mem_iff.mpr
    (Nat.lt_of_lt_of_le (theorem_7_4_cover_mem_iff.mp hi) hst)

/-- Helper for Theorem 7.4: the prefix cover `{i | i < t}` has exactly `t` elements when
`t ≤ n`. -/
theorem theorem_7_4_cover_card
    (t : ℕ)
    (ht : t ≤ n) :
    (theorem_7_4_cover (n := n) t).card = t := by
  -- Reindex the prefix cover by `Fin t`.
  rw [theorem_7_4_cover_eq_castLEImage (n := n) t ht]
  simp

/-- Helper for Theorem 7.4: filtering the prefix cover by `s ≤ i` removes the shorter prefix
`theorem_7_4_cover s`. -/
theorem theorem_7_4_cover_filter_ge_eq_sdiff
    (t s : ℕ) :
    (theorem_7_4_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) =
      theorem_7_4_cover t \ theorem_7_4_cover s := by
  -- On the prefix cover, `s ≤ i` is equivalent to `i ∉ theorem_7_4_cover s`.
  ext i
  simp [theorem_7_4_cover_mem_iff]

/-- Helper for Theorem 7.4: the weights on the suffix `{i ∈ C | s ≤ i}` sum to `μ_t - μ_s`. -/
theorem theorem_7_4_cover_suffix_sum_eq
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hst : s ≤ t) :
    ((theorem_7_4_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).sum weights =
      theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s := by
  have hs : s ≤ n := Nat.le_trans hst ht
  -- Rewrite the suffix as the difference between the long and short prefix covers.
  rw [theorem_7_4_cover_filter_ge_eq_sdiff]
  have hsum :
      (theorem_7_4_cover t \ theorem_7_4_cover s).sum weights +
          (theorem_7_4_cover s).sum weights =
        (theorem_7_4_cover t).sum weights := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff (theorem_7_4_cover_subset (n := n) hst) (f := weights))
  have hmu_prefix_eq :
      theorem_7_4_mu weights s hs s = theorem_7_4_mu weights t ht s := by
    -- The first `s` partial sums are independent of the larger ambient prefix length `t`.
    exact theorem_7_4_mu_prefix_eq weights hs ht hst
  -- Compare the two prefix sums using the canonical `μ`-normalization.
  rw [theorem_7_4_cover_sum_eq_mu weights t ht, theorem_7_4_cover_sum_eq_mu weights s hs] at hsum
  rw [hmu_prefix_eq] at hsum
  omega

/-- Helper for Theorem 7.4: the suffix `{i ∈ C | s ≤ i}` contains exactly the last `t - s`
cover indices. -/
theorem theorem_7_4_cover_suffix_card_eq
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hst : s ≤ t) :
    ((theorem_7_4_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).card = t - s := by
  have hs : s ≤ n := Nat.le_trans hst ht
  -- Rewrite the suffix as a set difference of the two prefix covers.
  rw [theorem_7_4_cover_filter_ge_eq_sdiff]
  -- The cardinals of the prefix covers are already known explicitly.
  rw [Finset.card_sdiff_of_subset (theorem_7_4_cover_subset (n := n) hst)]
  rw [theorem_7_4_cover_card (n := n) t ht, theorem_7_4_cover_card (n := n) s hs]

/-- Helper for Theorem 7.4: the explicit source witness is supported on the off-cover index `j`
and the cover suffix `{i ∈ C | s ≤ i}`. -/
private def theorem_7_4_suffixWitnessSupport
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Finset (Fin n) :=
  insert j ((theorem_7_4_cover t).filter fun i : Fin n ↦ s ≤ (i : ℕ))

/-- Helper for Theorem 7.4: the source suffix witness is the binary indicator of the support
`{j} ∪ {i ∈ C | s ≤ i}`. -/
private def theorem_7_4_suffixWitness
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Fin n → ℝ :=
  fun i ↦ if i ∈ theorem_7_4_suffixWitnessSupport t j s then 1 else 0

/-- Helper for Theorem 7.4: an off-cover index never belongs to the chosen cover suffix. -/
private theorem theorem_7_4_not_mem_cover_suffix
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ) :
    j ∉ (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) := by
  -- The suffix is contained in the cover, so an off-cover index cannot lie in it.
  intro hjSuffix
  exact hj ((Finset.mem_filter.mp hjSuffix).1)

/-- Helper for Theorem 7.4: the indicator witness is the sum of the cover indicator on the suffix
and the singleton vector at the off-cover index. -/
private theorem theorem_7_4_suffixWitness_eq
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ) :
    theorem_7_4_suffixWitness t j s =
      cover_indicator ((theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))) +
        Pi.single j (1 : ℝ) := by
  funext i
  by_cases hij : i = j
  · subst i
    have hjsuffix :
        j ∉ (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) :=
      theorem_7_4_not_mem_cover_suffix (j := j) hj s
    simp [theorem_7_4_suffixWitness, theorem_7_4_suffixWitnessSupport, cover_indicator, hjsuffix]
  · by_cases hi :
      i ∈ (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
    · simp [theorem_7_4_suffixWitness, theorem_7_4_suffixWitnessSupport, cover_indicator, hi, hij]
    · simp [theorem_7_4_suffixWitness, theorem_7_4_suffixWitnessSupport, cover_indicator, hi, hij]

/-- Helper for Theorem 7.4: the witness weight is the off-cover weight plus the chosen suffix
weight. -/
private theorem theorem_7_4_suffixWitnessWeight
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    ∑ i, (weights i : ℝ) * theorem_7_4_suffixWitness t j s i =
      (weights j : ℝ) +
        (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s : ℕ) : ℝ)) := by
  let suffix :=
    (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum :
      suffix.sum weights =
        theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s := by
    simpa [suffix] using theorem_7_4_cover_suffix_sum_eq weights t ht s hst
  -- Rewrite the witness as the sum of the suffix indicator and the singleton at `j`.
  calc
    ∑ i, (weights i : ℝ) * theorem_7_4_suffixWitness t j s i
      = (fun i ↦ (weights i : ℝ)) ⬝ᵥ theorem_7_4_suffixWitness t j s := by
          simp [dotProduct]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [theorem_7_4_suffixWitness_eq (j := j) hj s]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ cover_indicator suffix +
          (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
          rw [dotProduct_add]
    _ = suffix.sum (fun i ↦ (weights i : ℝ)) + weights j := by
          rw [dotProduct_comm, coverIndicator_dot_eq_sum]
          simp
    _ = (((suffix.sum weights : ℕ) : ℝ)) + weights j := by
          rw [Nat.cast_sum]
    _ =
        (weights j : ℝ) +
          (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s : ℕ) : ℝ)) := by
          rw [hsuffix_sum]
          ring

/-- Helper for Theorem 7.4: any coefficient vector that equals `1` on the cover evaluates on the
suffix witness as `α j + (t - s)`. -/
private theorem theorem_7_4_suffixWitnessCoeff
    (t : ℕ)
    (ht : t ≤ n)
    {α : Fin n → ℝ}
    (hαcover : ∀ i ∈ theorem_7_4_cover t, α i = 1)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    α ⬝ᵥ theorem_7_4_suffixWitness t j s = α j + (t - s : ℝ) := by
  let suffix :=
    (theorem_7_4_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum_one :
      suffix.sum α = suffix.sum (fun _ ↦ (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hαcover i ((Finset.mem_filter.mp hi).1)
  calc
    α ⬝ᵥ theorem_7_4_suffixWitness t j s
      = α ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [theorem_7_4_suffixWitness_eq (j := j) hj s]
    _ = α ⬝ᵥ cover_indicator suffix + α ⬝ᵥ Pi.single j (1 : ℝ) := by
          rw [dotProduct_add]
    _ = cover_indicator suffix ⬝ᵥ α + α j := by
          rw [dotProduct_comm]
          simp
    _ = suffix.sum α + α j := by
          rw [coverIndicator_dot_eq_sum]
    _ = (suffix.card : ℝ) + α j := by
          rw [hsuffix_sum_one]
          simp
    _ = α j + (t - s : ℝ) := by
          rw [theorem_7_4_cover_suffix_card_eq (n := n) t ht s hst, Nat.cast_sub hst]
          ring

/-- Helper for Theorem 7.4: the suffix witness is feasible whenever its normalized total weight
fits within the residual capacity. -/
private theorem theorem_7_4_suffixWitnessFeasible
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (s : ℕ)
    (hst : s ≤ t)
    (hfeasible :
      (weights j : ℝ) +
        (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s : ℕ) : ℝ)) ≤ capacity) :
    theorem_7_4_suffixWitness t j s ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · -- The witness is an indicator, so every coordinate is either `0` or `1`.
    intro i
    by_cases hi : i ∈ theorem_7_4_suffixWitnessSupport t j s
    · right
      simp [theorem_7_4_suffixWitness, hi]
    · left
      simp [theorem_7_4_suffixWitness, hi]
  · -- Rewrite the witness weight through the normalized suffix sum and apply the residual bound.
    rw [theorem_7_4_suffixWitnessWeight (weights := weights) (t := t) (ht := ht) (j := j) hj s hst]
    exact hfeasible

/-- Helper for Theorem 7.4: if the off-cover weight lies below `μ_s - λ`, then the suffix
starting at `s` together with the off-cover item fits within the knapsack capacity. -/
theorem theorem_7_4_suffixResidualLeCapacity
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    {s : ℕ}
    (hst : s ≤ t)
    (hμs :
      theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht s)
    (hupper :
      weights j ≤ theorem_7_4_mu weights t ht s -
        theorem_7_4_cover_excess weights capacity t ht) :
    weights j + (theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht s) ≤ capacity := by
  have hmu_t_ge_capacity : capacity ≤ theorem_7_4_mu weights t ht t := by
    have hcover : IsKnapsackCover weights capacity (theorem_7_4_cover t) := inferInstance
    have hcover_lt :
        capacity < (theorem_7_4_cover t).sum weights :=
      (isKnapsackCover_iff weights capacity (theorem_7_4_cover t)).mp hcover
    rw [theorem_7_4_cover_sum_eq_mu weights t ht] at hcover_lt
    exact Nat.le_of_lt hcover_lt
  have hupper' :
      weights j + theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht s :=
    (Nat.le_sub_iff_add_le hμs).mp hupper
  have hs_le_n : s ≤ n := Nat.le_trans hst ht
  have hmu_prefix_le :
      theorem_7_4_mu weights t ht s ≤ theorem_7_4_mu weights t ht t := by
    have hnonnegative :
        ∀ i ∈ theorem_7_4_cover (n := n) t,
          i ∉ theorem_7_4_cover (n := n) s → 0 ≤ weights i := by
      intro i hi hino
      exact Nat.zero_le _
    have hprefix_sum_le :
        (theorem_7_4_cover (n := n) s).sum weights ≤
          (theorem_7_4_cover (n := n) t).sum weights :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (theorem_7_4_cover_subset (n := n) hst)
        hnonnegative
    have hprefix_sum_eq :
        (theorem_7_4_cover (n := n) s).sum weights =
          theorem_7_4_mu weights t ht s := by
      calc
        (theorem_7_4_cover (n := n) s).sum weights
            = theorem_7_4_mu weights s hs_le_n s := by
                rw [theorem_7_4_cover_sum_eq_mu]
        _ = theorem_7_4_mu weights t ht s := by
              rw [theorem_7_4_mu_prefix_eq weights hs_le_n ht hst]
    have hcover_sum_eq :
        (theorem_7_4_cover (n := n) t).sum weights =
          theorem_7_4_mu weights t ht t := by
      rw [theorem_7_4_cover_sum_eq_mu]
    rw [hprefix_sum_eq, hcover_sum_eq] at hprefix_sum_le
    exact hprefix_sum_le
  -- Rewrite the residual-capacity inequality into the target suffix form once.
  have hupper'' :
      weights j + (theorem_7_4_mu weights t ht t - capacity) ≤ theorem_7_4_mu weights t ht s := by
    simpa [theorem_7_4_cover_excess] using hupper'
  omega

/-- Helper for Theorem 7.4: the exact interval hypothesis already forces the upper bound
`α j ≤ h` from validity. -/
theorem theorem_7_4_exact_interval_upper_bound
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {α : Fin n → ℝ}
    (hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_exact_interval_condition weights capacity t ht j h) :
    α j ≤ h := by
  have hαcover :
      ∀ i ∈ theorem_7_4_cover t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).1
  have hαvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover t)) :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).2
  -- Move validity from the convex hull owner back to the binary knapsack set.
  have hαvalid_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαvalid_poly
    exact is_valid_inequality_convexHull_iff.mp hαvalid_poly
  have hs : h + 1 ≤ t := Nat.succ_le_of_lt hh
  have hlam_le_mu :
      theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht (h + 1) := by
    -- Minimality bounds the cover excess by every cover weight, hence by the next partial sum.
    rw [theorem_7_4_mu_succ_of_lt weights t ht h hh]
    have hlam_le_weight :
        theorem_7_4_cover_excess weights capacity t ht ≤
          theorem_7_4_cover_weight weights ht ⟨h, hh⟩ :=
      theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h, hh⟩
    omega
  have hfeasible_nat :
      weights j + (theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 1)) ≤
        capacity :=
    theorem_7_4_suffixResidualLeCapacity
      weights capacity t ht hC hs hlam_le_mu hinterval.2
  have hfeasible :
      (weights j : ℝ) +
          (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 1) : ℕ) : ℝ)) ≤
        capacity := by
    exact_mod_cast hfeasible_nat
  have hx_mem :
      theorem_7_4_suffixWitness t j (h + 1) ∈
        zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) :=
    theorem_7_4_suffixWitnessFeasible weights capacity t ht hj (h + 1) hs hfeasible
  have hx_valid := hαvalid_set hx_mem
  have hcoeff := theorem_7_4_suffixWitnessCoeff t ht hαcover hj (h + 1) hs
  have hcover_rhs :
      cover_inequality_rhs (theorem_7_4_cover (n := n) t) = (t : ℝ) - 1 := by
    rw [cover_inequality_rhs_eq, theorem_7_4_cover_card (n := n) t ht]
  have hsucc_real :
      ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by
    norm_num
  -- Evaluate the witness and compare it with the cover right-hand side.
  rw [hcoeff, hcover_rhs] at hx_valid
  linarith [hsucc_real]

/-- Helper for Theorem 7.4: the boundary interval hypothesis still gives the upper bound
`α j ≤ h + 1` from validity. -/
theorem theorem_7_4_boundary_interval_upper_bound
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {α : Fin n → ℝ}
    (hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_boundary_interval_condition weights capacity t ht j h) :
    α j ≤ h + 1 := by
  have hαcover :
      ∀ i ∈ theorem_7_4_cover t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).1
  have hαvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover t)) :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).2
  -- Move validity from the convex hull owner back to the binary knapsack set.
  have hαvalid_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαvalid_poly
    exact is_valid_inequality_convexHull_iff.mp hαvalid_poly
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hh) with hs | hs
  · have hs' : h + 2 ≤ t := Nat.succ_le_of_lt hs
    have hlam_le_mu :
        theorem_7_4_cover_excess weights capacity t ht ≤ theorem_7_4_mu weights t ht (h + 2) := by
      -- In the strict case, the next cover weight still dominates the cover excess.
      rw [theorem_7_4_mu_succ_of_lt weights t ht (h + 1) hs]
      have hlam_le_weight :
          theorem_7_4_cover_excess weights capacity t ht ≤
            theorem_7_4_cover_weight weights ht ⟨h + 1, hs⟩ :=
        theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h + 1, hs⟩
      omega
    have hupper :
        weights j ≤ theorem_7_4_mu weights t ht (h + 2) -
          theorem_7_4_cover_excess weights capacity t ht := by
      have hmu_gap :
          theorem_7_4_mu weights t ht (h + 1) ≤
            theorem_7_4_mu weights t ht (h + 2) -
              theorem_7_4_cover_excess weights capacity t ht := by
        rw [theorem_7_4_mu_succ_of_lt weights t ht (h + 1) hs]
        have hlam_le_weight :
            theorem_7_4_cover_excess weights capacity t ht ≤
              theorem_7_4_cover_weight weights ht ⟨h + 1, hs⟩ :=
          theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h + 1, hs⟩
        omega
      have hweights_le_mu : weights j ≤ theorem_7_4_mu weights t ht (h + 1) :=
        Nat.le_of_lt hinterval.2
      exact le_trans hweights_le_mu hmu_gap
    have hfeasible_nat :
        weights j + (theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 2)) ≤
          capacity :=
      theorem_7_4_suffixResidualLeCapacity
        weights capacity t ht hC hs' hlam_le_mu hupper
    have hfeasible :
        (weights j : ℝ) +
            (((theorem_7_4_mu weights t ht t - theorem_7_4_mu weights t ht (h + 2) : ℕ) : ℝ)) ≤
          capacity := by
      exact_mod_cast hfeasible_nat
    have hx_mem :
        theorem_7_4_suffixWitness t j (h + 2) ∈
          zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) :=
      theorem_7_4_suffixWitnessFeasible weights capacity t ht hj (h + 2) hs' hfeasible
    have hx_valid := hαvalid_set hx_mem
    have hcoeff := theorem_7_4_suffixWitnessCoeff t ht hαcover hj (h + 2) hs'
    have hcover_rhs :
        cover_inequality_rhs (theorem_7_4_cover (n := n) t) = (t : ℝ) - 1 := by
      rw [cover_inequality_rhs_eq, theorem_7_4_cover_card (n := n) t ht]
    have hsucc_real :
        ((h + 2 : ℕ) : ℝ) = (h : ℝ) + 2 := by
      norm_num
    -- The shifted suffix witness leaves room for at most the coefficient `h + 1`.
    rw [hcoeff, hcover_rhs] at hx_valid
    linarith [hsucc_real]
  · have hmu_t_ge_capacity : capacity ≤ theorem_7_4_mu weights t ht t := by
      have hcover : IsKnapsackCover weights capacity (theorem_7_4_cover t) := inferInstance
      have hcover_lt :
          capacity < (theorem_7_4_cover t).sum weights :=
        (isKnapsackCover_iff weights capacity (theorem_7_4_cover t)).mp hcover
      rw [theorem_7_4_cover_sum_eq_mu weights t ht] at hcover_lt
      exact Nat.le_of_lt hcover_lt
    have hcapacity_eq :
        theorem_7_4_mu weights t ht (h + 1) -
            theorem_7_4_cover_excess weights capacity t ht =
          capacity := by
      have hs' : h + 1 = t := by
        simpa using hs
      rw [hs', theorem_7_4_cover_excess]
      omega
    have hcapacity_lt : capacity < weights j := by
      simpa [hcapacity_eq] using hinterval.1
    -- Route correction: the terminal boundary case is impossible because the open interval becomes
    -- `capacity < weights j < μ_t`, contradicting the standing item bound `weights j ≤ capacity`.
    exact (False.elim <| not_lt_of_ge (hweights_le j) hcapacity_lt)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the position of an element in
a strictly increasing finite enumeration does not exceed its value. -/
private theorem theorem_7_4_fin_le_strictMono_val
    {q r : ℕ}
    (f : Fin q → Fin r)
    (hf : StrictMono f)
    (i : Fin q) :
    (i : ℕ) ≤ (f i : ℕ) := by
  -- Induction along the enumeration compares each position with its strictly larger successor.
  have haux : ∀ k, ∀ hk : k < q, k ≤ (f ⟨k, hk⟩ : ℕ) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact Nat.zero_le _
    | succ k ih =>
        intro hk
        have hk' : k < q := Nat.lt_trans (Nat.lt_succ_self k) hk
        have hfinStep : (⟨k, hk'⟩ : Fin q) < ⟨k + 1, hk⟩ := by simp
        have hstep : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := hf hfinStep
        exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hk') hstep)
  exact haux i i.isLt

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: any subset of the descending
prefix cover weighs at most the initial prefix of the same cardinality. -/
private theorem descendingPrefixSubsetSum_le_muCard
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : theorem_7_4_cover_weights_descending weights ht)
    (S : Finset (Fin n))
    (hS : S ⊆ theorem_7_4_cover t) :
    S.sum weights ≤ theorem_7_4_mu weights t ht S.card := by
  classical
  have hcard : S.card ≤ t := by
    calc
      S.card ≤ (theorem_7_4_cover (n := n) t).card := Finset.card_le_card hS
      _ = t := theorem_7_4_cover_card t ht
  let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  have hterm :
      ∀ i : Fin S.card, weights (e i) ≤ weights (i.castLE (Nat.le_trans hcard ht)) := by
    intro i
    have heiS : e i ∈ S := by simp [e]
    have heiMem : e i ∈ theorem_7_4_cover (n := n) t := hS heiS
    let ei : Fin t := ⟨(e i : ℕ), theorem_7_4_cover_mem_iff.mp heiMem⟩
    have hie : i.castLE hcard ≤ ei := by
      rw [Fin.le_iff_val_le_val]
      exact theorem_7_4_fin_le_strictMono_val e e.strictMono i
    have hweight := hdescending hie
    simpa [theorem_7_4_cover_weights_descending, theorem_7_4_cover_weight, e, ei] using hweight
  -- Reindex `S` increasingly and compare each selected position with the same prefix position.
  calc
    S.sum weights = ∑ i : Fin S.card, weights (e i) := by
      calc
        S.sum weights =
            ((Finset.univ : Finset (Fin S.card)).map (S.orderEmbOfFin rfl).toEmbedding).sum
              weights := by rw [S.map_orderEmbOfFin_univ rfl]
        _ = ∑ i : Fin S.card, weights (e i) := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ i : Fin S.card, weights (i.castLE (Nat.le_trans hcard ht)) := by
      exact Finset.sum_le_sum fun i _ ↦ hterm i
    _ = theorem_7_4_mu weights t ht S.card := by
      rw [theorem_7_4_mu, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hit : (i : ℕ) < t := Nat.lt_of_lt_of_le i.isLt hcard
      rw [dif_pos hit]
      exact congrArg weights (Fin.ext rfl)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the partial sums of the
nonnegative cover weights are monotone in their length. -/
private theorem theorem_7_4_mu_mono
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    {a b : ℕ}
    (hab : a ≤ b) :
    theorem_7_4_mu weights t ht a ≤ theorem_7_4_mu weights t ht b := by
  -- Extend the shorter range inside the longer one; all omitted summands are nonnegative.
  unfold theorem_7_4_mu
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hab)
      (fun _ _ _ ↦ Nat.zero_le _)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: replacing a selected item by
a no-heavier family of zero coordinates preserves binary knapsack feasibility. -/
private theorem theorem_7_4_coverExchange_mem_knapsack
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    {x : Fin n → ℝ}
    (hx : x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
    {j : Fin n}
    (hxj : x j = 1)
    (H : Finset (Fin n))
    (hjH : j ∉ H)
    (hzero : ∀ i ∈ H, x i = 0)
    (hweight : H.sum weights ≤ weights j) :
    x + cover_indicator H - Pi.single j (1 : ℝ) ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  have hxData := (mem_zero_one_knapsack_set_iff _ _ _).mp hx
  let y : Fin n → ℝ := x + cover_indicator H - Pi.single j (1 : ℝ)
  change y ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    by_cases hiH : i ∈ H
    · have hij : i ≠ j := by
        intro hij
        subst i
        exact hjH hiH
      right
      simp [y, Pi.add_apply, Pi.sub_apply, cover_indicator, hiH, hzero i hiH, hij]
    · by_cases hij : i = j
      · subst i
        left
        simp [y, Pi.add_apply, Pi.sub_apply, cover_indicator, hiH, hxj]
      · rcases hxData.1 i with hxi | hxi
        · left
          simp [y, Pi.add_apply, Pi.sub_apply, cover_indicator, hiH, hxi, hij]
        · right
          simp [y, Pi.add_apply, Pi.sub_apply, cover_indicator, hiH, hxi, hij]
  · have hweightReal : ((H.sum weights : ℕ) : ℝ) ≤ weights j := by
      exact_mod_cast hweight
    have hdot :
        ∑ i, (weights i : ℝ) * y i =
          ∑ i, (weights i : ℝ) * x i + ((H.sum weights : ℕ) : ℝ) - weights j := by
      calc
        ∑ i, (weights i : ℝ) * y i =
            (fun i ↦ (weights i : ℝ)) ⬝ᵥ
              (x + cover_indicator H - Pi.single j (1 : ℝ)) := by
                simp [y, dotProduct]
        _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ x +
              (fun i ↦ (weights i : ℝ)) ⬝ᵥ cover_indicator H -
                (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
                  rw [dotProduct_sub, dotProduct_add]
        _ = ∑ i, (weights i : ℝ) * x i +
              H.sum (fun i ↦ (weights i : ℝ)) - weights j := by
                rw [dotProduct_comm (fun i ↦ (weights i : ℝ)) (cover_indicator H),
                  coverIndicator_dot_eq_sum]
                simp [dotProduct, Pi.single_apply]
        _ = ∑ i, (weights i : ℝ) * x i + ((H.sum weights : ℕ) : ℝ) - weights j := by
              rw [Nat.cast_sum]
    -- The exchange does not increase total weight, so the old capacity bound closes the goal.
    rw [hdot]
    linarith [hxData.2]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: exchanging a selected
off-cover item for `h` zero cover coordinates identifies the updated and old objectives. -/
private theorem theorem_7_4_updatedCoeff_dot_exchange
    {t h : ℕ}
    {x α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (hxj : x j = 1)
    (H : Finset (Fin n))
    (hHC : H ⊆ theorem_7_4_cover t)
    (hHcard : H.card = h) :
    lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j (h : ℝ)) ⬝ᵥ x =
      lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ
        (x + cover_indicator H - Pi.single j (1 : ℝ)) := by
  have hjH : j ∉ H := fun hj' ↦ hj (hHC hj')
  have hHcoeff :
      H.sum (lifted_cover_inequality_coeff (theorem_7_4_cover t) α) = (h : ℝ) := by
    calc
      H.sum (lifted_cover_inequality_coeff (theorem_7_4_cover t) α) =
          H.sum (fun _ ↦ (1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [lifted_cover_inequality_coeff, hHC hi]
      _ = (H.card : ℝ) := by simp
      _ = (h : ℝ) := by rw [hHcard]
  have hbasej : lifted_cover_inequality_coeff (theorem_7_4_cover t) α j = α j := by
    simp [lifted_cover_inequality_coeff, hj]
  have hupdate :
      lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j (h : ℝ)) =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α +
          Pi.single j ((h : ℝ) - α j) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [lifted_cover_inequality_coeff, hj]
    · by_cases hi : i ∈ theorem_7_4_cover t
      · simp [lifted_cover_inequality_coeff, hi, hij]
      · simp [lifted_cover_inequality_coeff, hi, hij, Function.update]
  have hleft :
      lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j (h : ℝ)) ⬝ᵥ x =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
          ((h : ℝ) - α j) := by
    rw [hupdate, add_dotProduct]
    simp [dotProduct, Pi.single_apply, hxj]
  have hright :
      lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ
          (x + cover_indicator H - Pi.single j (1 : ℝ)) =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
          (h : ℝ) - α j := by
    calc
      lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ
            (x + cover_indicator H - Pi.single j (1 : ℝ)) =
          lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
            lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ cover_indicator H -
              lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ
                Pi.single j (1 : ℝ) := by
                  rw [dotProduct_sub, dotProduct_add]
      _ = lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
            H.sum (lifted_cover_inequality_coeff (theorem_7_4_cover t) α) -
              lifted_cover_inequality_coeff (theorem_7_4_cover t) α j := by
                rw [dotProduct_comm
                    (lifted_cover_inequality_coeff (theorem_7_4_cover t) α)
                    (cover_indicator H),
                  coverIndicator_dot_eq_sum]
                simp [dotProduct, Pi.single_apply]
      _ = lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
            (h : ℝ) - α j := by rw [hHcoeff, hbasej]
  -- Both objectives are the same singleton perturbation of the old lifted objective.
  rw [hleft, hright]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: if the first `h` cover
weights fit under an off-cover weight, replacing that lifting coefficient by `h` remains valid. -/
private theorem validCoefficientUpdateOfMuLeWeight
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hdescending : theorem_7_4_cover_weights_descending weights ht)
    {α : Fin n → ℝ}
    (hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality
        weights capacity (theorem_7_4_cover t))
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hmu : theorem_7_4_mu weights t ht h ≤ weights j) :
    is_valid_inequality
      (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
      (lifted_cover_inequality_coeff
        (theorem_7_4_cover t) (Function.update α j (h : ℝ)))
      (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
  classical
  have hαcover : ∀ i ∈ theorem_7_4_cover t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).1
  have hαfixed :
      lifted_cover_inequality_coeff (theorem_7_4_cover t) α = α := by
    funext i
    by_cases hi : i ∈ theorem_7_4_cover t
    · simp [lifted_cover_inequality_coeff, hi, hαcover i hi]
    · simp [lifted_cover_inequality_coeff, hi]
  have hαpoly := (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).2
  have hαset :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (lifted_cover_inequality_coeff (theorem_7_4_cover t) α)
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαpoly
    simpa [hαfixed] using is_valid_inequality_convexHull_iff.mp hαpoly
  rw [zero_one_knapsack_polytope_eq_convexHull]
  refine is_valid_inequality_convexHull_iff.mpr ?_
  intro x hx
  have hxData := (mem_zero_one_knapsack_set_iff _ _ _).mp hx
  rcases hxData.1 j with hxj | hxj
  · -- When the pivot is zero, updating its coefficient does not alter the objective.
    have hcoeffEq :
        lifted_cover_inequality_coeff
              (theorem_7_4_cover t) (Function.update α j (h : ℝ)) ⬝ᵥ x =
          lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x := by
      rw [dotProduct, dotProduct]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hij : i = j
      · subst i
        simp [lifted_cover_inequality_coeff, hj, hxj]
      · simp [lifted_cover_inequality_coeff, hij, Function.update]
    rw [hcoeffEq]
    exact hαset hx
  · let Z : Finset (Fin n) :=
      (theorem_7_4_cover t).filter (fun i ↦ x i = 0)
    have hZsubset : Z ⊆ theorem_7_4_cover t := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    have hZzero : ∀ i ∈ Z, x i = 0 := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hZcard : h ≤ Z.card := by
      by_contra hnot
      have hZcard_lt : Z.card < h := Nat.lt_of_not_ge hnot
      have hZsum_le_muCard : Z.sum weights ≤ theorem_7_4_mu weights t ht Z.card :=
        descendingPrefixSubsetSum_le_muCard weights t ht hdescending Z hZsubset
      have hZsum_le_weight : Z.sum weights ≤ weights j :=
        le_trans hZsum_le_muCard
          (le_trans (theorem_7_4_mu_mono weights t ht (Nat.le_of_lt hZcard_lt)) hmu)
      let X : Finset (Fin n) := Finset.univ.filter (fun i ↦ x i = 1)
      have hXone : ∀ i ∈ X, x i = 1 := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hXzero : ∀ i ∉ X, x i = 0 := by
        intro i hi
        rcases hxData.1 i with hxi | hxi
        · exact hxi
        · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩))
      have hweightSupport :
          ∑ i, (weights i : ℝ) * x i = ((X.sum weights : ℕ) : ℝ) := by
        calc
          ∑ i, (weights i : ℝ) * x i =
              ∑ i, if i ∈ X then (weights i : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hiX : i ∈ X
                · simp [hiX, hXone i hiX]
                · simp [hiX, hXzero i hiX]
          _ = X.sum (fun i ↦ (weights i : ℝ)) := by
                simp only [X, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
          _ = ((X.sum weights : ℕ) : ℝ) := by rw [Nat.cast_sum]
      have hXcapacity : X.sum weights ≤ capacity := by
        have hreal : ((X.sum weights : ℕ) : ℝ) ≤ capacity := by
          simpa [hweightSupport] using hxData.2
        exact_mod_cast hreal
      have hjX : j ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxj⟩
      have hselectedSubset :
          insert j (theorem_7_4_cover t \ Z) ⊆ X := by
        intro i hi
        rcases Finset.mem_insert.mp hi with hij | hiCover
        · simpa [hij] using hjX
        · have hiC : i ∈ theorem_7_4_cover t := (Finset.mem_sdiff.mp hiCover).1
          have hiZ : i ∉ Z := (Finset.mem_sdiff.mp hiCover).2
          rcases hxData.1 i with hxi | hxi
          · exact False.elim (hiZ (Finset.mem_filter.mpr ⟨hiC, hxi⟩))
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩
      have hselectedWeight :
          (insert j (theorem_7_4_cover t \ Z)).sum weights ≤ X.sum weights :=
        Finset.sum_le_sum_of_subset_of_nonneg hselectedSubset
          (fun _ _ _ ↦ Nat.zero_le _)
      have hjDiff : j ∉ theorem_7_4_cover t \ Z := by
        intro hj'
        exact hj (Finset.mem_sdiff.mp hj').1
      have hcoverSplit :
          Z.sum weights + (theorem_7_4_cover t \ Z).sum weights =
            (theorem_7_4_cover t).sum weights := by
        simpa [add_comm] using Finset.sum_sdiff hZsubset (f := weights)
      have hcoverLe : (theorem_7_4_cover t).sum weights ≤ X.sum weights := by
        calc
          (theorem_7_4_cover t).sum weights =
              Z.sum weights + (theorem_7_4_cover t \ Z).sum weights := hcoverSplit.symm
          _ ≤ weights j + (theorem_7_4_cover t \ Z).sum weights :=
            Nat.add_le_add_right hZsum_le_weight _
          _ = (insert j (theorem_7_4_cover t \ Z)).sum weights := by
            rw [Finset.sum_insert hjDiff]
          _ ≤ X.sum weights := hselectedWeight
      have hcoverLt : capacity < (theorem_7_4_cover t).sum weights :=
        (isKnapsackCover_iff weights capacity (theorem_7_4_cover t)).mp hC.toIsKnapsackCover
      omega
    obtain ⟨H, hHZ, hHcard⟩ := Finset.exists_subset_card_eq hZcard
    have hHC : H ⊆ theorem_7_4_cover t := Set.Subset.trans hHZ hZsubset
    have hjH : j ∉ H := fun hj' ↦ hj (hHC hj')
    have hHzero : ∀ i ∈ H, x i = 0 := by
      intro i hi
      exact hZzero i (hHZ hi)
    have hHweight : H.sum weights ≤ weights j := by
      have hmuAtCard : theorem_7_4_mu weights t ht H.card ≤ weights j := by
        simpa [hHcard] using hmu
      exact le_trans
        (descendingPrefixSubsetSum_le_muCard weights t ht hdescending H hHC)
        hmuAtCard
    have hy :
        x + cover_indicator H - Pi.single j (1 : ℝ) ∈
          zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) :=
      theorem_7_4_coverExchange_mem_knapsack
        weights capacity hx hxj H hjH hHzero hHweight
    have hobjective :=
      theorem_7_4_updatedCoeff_dot_exchange (α := α) hj hxj H hHC hHcard
    -- Apply the old valid lifting to the exchanged point and transport its objective back to `x`.
    rw [hobjective]
    exact hαset hy

/-- Helper for Theorem 7.4: every coordinate of a `0,1` knapsack polytope point lies in the unit
interval. -/
private theorem theorem_7_4_polytopeCoordBounds
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    {x : Fin n → ℝ}
    (hx :
      x ∈ zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
    (j : Fin n) :
    0 ≤ x j ∧ x j ≤ 1 := by
  have hlower_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (-Pi.single j (1 : ℝ))
        0 := by
    -- On binary points, the lower bound is just `-x_j ≤ 0`.
    intro y hy
    rcases ((mem_zero_one_knapsack_set_iff _ _ _).mp hy).1 j with hyj | hyj
    · simp [hyj, dotProduct, Pi.single_apply]
    · simp [hyj, dotProduct, Pi.single_apply]
  have hupper_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Pi.single j (1 : ℝ))
        1 := by
    -- On binary points, the upper bound is exactly `x_j ≤ 1`.
    intro y hy
    rcases ((mem_zero_one_knapsack_set_iff _ _ _).mp hy).1 j with hyj | hyj
    · simp [hyj, dotProduct, Pi.single_apply]
    · simp [hyj, dotProduct, Pi.single_apply]
  have hlower_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (-Pi.single j (1 : ℝ))
        0 := by
    -- Validity passes from the binary set to its convex hull owner.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hlower_set
  have hupper_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Pi.single j (1 : ℝ))
        1 := by
    -- Validity passes from the binary set to its convex hull owner.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hupper_set
  refine ⟨?_, ?_⟩
  · -- Evaluate the lower-bound inequality at `x`.
    have hxlower := hlower_poly hx
    simpa [dotProduct, Pi.single_apply] using hxlower
  · -- Evaluate the upper-bound inequality at `x`.
    have hxupper := hupper_poly hx
    simpa [dotProduct, Pi.single_apply] using hxupper

/-- Helper for Theorem 7.4: increasing an off-cover coefficient only changes the lifted cover
coefficient vector by a singleton at that coordinate. -/
private theorem theorem_7_4_updatedLiftedCoeff_eq
    {t : ℕ}
    {α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    (σ : ℝ) :
    lifted_cover_inequality_coeff (theorem_7_4_cover t) (Function.update α j σ) =
      lifted_cover_inequality_coeff (theorem_7_4_cover t) α +
        Pi.single j (σ - α j) := by
  -- Route correction: keep the comparison on the original owner and isolate the coefficient
  -- update as a single-coordinate perturbation.
  funext i
  by_cases hij : i = j
  · subst i
    simp [lifted_cover_inequality_coeff, hj]
  · by_cases hi : i ∈ theorem_7_4_cover t
    · simp [lifted_cover_inequality_coeff, hi, hij]
    · simp [lifted_cover_inequality_coeff, hi, hij, Function.update]

/-- Helper for Theorem 7.4: if a strictly larger off-cover coefficient is still valid, every point
on the old lifted-cover face has zero in that coordinate. -/
private theorem theorem_7_4_faceCoordinateZero_of_strict_update
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    {α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {σ : ℝ}
    (hασ : α j < σ)
    (hvalidσ :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (lifted_cover_inequality_coeff (theorem_7_4_cover t) (Function.update α j σ))
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t))) :
    ∀ ⦃x : Fin n → ℝ⦄,
      x ∈ lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) (theorem_7_4_cover t) α →
        x j = 0 := by
  intro x hx
  have hxFace : x ∈ face_set
      (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
      (lifted_cover_inequality_coeff (theorem_7_4_cover t) α)
      (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    simpa [lifted_cover_face] using hx
  rcases mem_face_set_iff.mp hxFace with ⟨hxP, hxEq⟩
  have hxUpdated : (lifted_cover_inequality_coeff
      (theorem_7_4_cover t) (Function.update α j σ)) ⬝ᵥ x ≤
        cover_inequality_rhs (theorem_7_4_cover t) :=
    hvalidσ hxP
  have hxNonneg : 0 ≤ x j :=
    (theorem_7_4_polytopeCoordBounds weights capacity hxP j).1
  have hxUpdatedEq :
      (lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j σ)) ⬝ᵥ x =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
          (σ - α j) * x j := by
    -- Expand the singleton perturbation and evaluate its dot product.
    rw [theorem_7_4_updatedLiftedCoeff_eq (t := t) (α := α) (j := j) hj σ, add_dotProduct]
    simp [dotProduct, Pi.single_apply]
  have hdiffPos : 0 < σ - α j := sub_pos.mpr hασ
  rw [hxUpdatedEq, hxEq] at hxUpdated
  rcases lt_or_eq_of_le hxNonneg with hxPos | hxZero
  · -- A positive `x_j` would make the stricter valid inequality exceed the old face value.
    have hprodPos : 0 < (σ - α j) * x j := mul_pos hdiffPos hxPos
    linarith
  · exact hxZero.symm

/-- Helper for Theorem 7.4: once the stricter updated inequality is valid, the old lifted-cover
face sits inside the updated face. -/
private theorem theorem_7_4_faceSubset_of_strict_update
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    {α : Fin n → ℝ}
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {σ : ℝ}
    (hασ : α j < σ)
    (hvalidσ :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (lifted_cover_inequality_coeff (theorem_7_4_cover t) (Function.update α j σ))
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t))) :
    lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) (theorem_7_4_cover t) α ⊆
      lifted_cover_face
        (fun i ↦ (weights i : ℝ))
        (capacity : ℝ)
        (theorem_7_4_cover t)
        (Function.update α j σ) := by
  intro x hx
  have hxFace : x ∈ face_set
      (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
      (lifted_cover_inequality_coeff (theorem_7_4_cover t) α)
      (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
    simpa [lifted_cover_face] using hx
  rcases mem_face_set_iff.mp hxFace with ⟨hxP, hxEq⟩
  have hxj0 :
      x j = 0 :=
    theorem_7_4_faceCoordinateZero_of_strict_update
      weights capacity t hj hασ hvalidσ hx
  have hxUpdatedEq :
      (lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j σ)) ⬝ᵥ x =
        lifted_cover_inequality_coeff (theorem_7_4_cover t) α ⬝ᵥ x +
          (σ - α j) * x j := by
    -- The singleton perturbation vanishes because `x_j = 0` on the old face.
    rw [theorem_7_4_updatedLiftedCoeff_eq (t := t) (α := α) (j := j) hj σ, add_dotProduct]
    simp [dotProduct, Pi.single_apply]
  -- Reuse the old face equality after deleting the zero pivot contribution.
  refine (mem_face_set_iff.mpr ?_)
  refine ⟨hxP, ?_⟩
  rw [hxUpdatedEq, hxEq, hxj0]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a valid single-coordinate
update of a facet lifting cannot exceed the facet's coefficient at that off-cover coordinate. -/
private theorem validUpdate_le_facetCoefficient
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (hweights_le : ∀ i, weights i ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    {α : Fin n → ℝ}
    (hαfacet : α ∈ theorem_7_4_facet_defining_liftings weights capacity t)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {σ : ℝ}
    (hvalidσ :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (lifted_cover_inequality_coeff
          (theorem_7_4_cover t) (Function.update α j σ))
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t))) :
    σ ≤ α j := by
  by_contra hnot
  have hstrict : α j < σ := lt_of_not_ge hnot
  let P := zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let c := lifted_cover_inequality_coeff (theorem_7_4_cover t) α
  let F := lifted_cover_face
    (fun i ↦ (weights i : ℝ)) (capacity : ℝ) (theorem_7_4_cover t) α
  have hfacet : IsFacetOf P F := by
    simpa [P, F] using
      (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hαfacet).2
  rcases (isFacetOf_iff.mp hfacet) with ⟨hFnonempty, -, hFcodim⟩
  obtain ⟨x₀, hx₀⟩ := hFnonempty
  have hzeroOn : ∀ {x : Fin n → ℝ}, x ∈ F → x j = 0 := by
    intro x hx
    have hxFace :
        x ∈ lifted_cover_face
          (fun i ↦ (weights i : ℝ)) (capacity : ℝ) (theorem_7_4_cover t) α := by
      simpa [F] using hx
    exact theorem_7_4_faceCoordinateZero_of_strict_update
      weights capacity t hj hstrict hvalidσ hxFace
  have hfaceHyperplane :
      F ⊆ {x | Pi.single j (1 : ℝ) ⬝ᵥ x = 0} := by
    intro x hx
    simpa [dotProduct, Pi.single_apply] using hzeroOn hx
  have hspanZero :
      (affineSpan ℝ F : Set (Fin n → ℝ)) ⊆
        {x | Pi.single j (1 : ℝ) ⬝ᵥ x = 0} :=
    affineSpan_subset_hyperplane_of_subset (c := Pi.single j (1 : ℝ)) hfaceHyperplane
  have hx₀span : x₀ ∈ affineSpan ℝ F := subset_affineSpan ℝ F hx₀
  have hdirectionCoord :
      (affineSpan ℝ F).direction ≤
        LinearMap.ker (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap := by
    intro v hv
    rw [LinearMap.mem_ker]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀span] at hv
    rcases hv with ⟨x, hxspan, rfl⟩
    have hxjZero : x j = 0 := by
      simpa [dotProduct, Pi.single_apply] using hspanZero hxspan
    simp [dotProductStrongDual_apply, dotProduct, Pi.single_apply, vsub_eq_sub,
      hxjZero, hzeroOn hx₀]
  have hsurjective :
      Function.Surjective
        (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap := by
    intro y
    refine ⟨y • Pi.single j (1 : ℝ), ?_⟩
    simp [dotProductStrongDual_apply, dotProduct, Pi.single_apply]
  have hrange :
      LinearMap.range (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  have hrangeFinrank :
      Module.finrank ℝ
          (LinearMap.range (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap) = 1 := by
    rw [hrange, finrank_top]
    simp
  have hkernelFinrank :
      Module.finrank ℝ
          (LinearMap.ker (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap) + 1 = n := by
    have hrankNull :=
      LinearMap.finrank_range_add_finrank_ker
        (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap
    rw [hrangeFinrank] at hrankNull
    simpa [Module.finrank_fintype_fun_eq_card, add_comm] using hrankNull
  have hoverweight :
      zero_one_knapsack_overweight_indices
          (fun i ↦ (weights i : ℝ)) (capacity : ℝ) = ∅ := by
    ext i
    simp [zero_one_knapsack_overweight_indices, hweights_le i]
  have hPdim : Module.finrank ℝ (affineSpan ℝ P).direction = n := by
    have hweightsNonnegative : ∀ i, 0 ≤ (weights i : ℝ) := by
      intro i
      positivity
    have hcapacityNonnegative : (0 : ℝ) ≤ capacity := by positivity
    simpa [P, hoverweight] using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        (fun i ↦ (weights i : ℝ))
        (capacity : ℝ)
        hweightsNonnegative
        hcapacityNonnegative
  have hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = n := by
    simpa [hPdim] using hFcodim
  have hdirectionEq :
      (affineSpan ℝ F).direction =
        LinearMap.ker (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap := by
    apply Submodule.eq_of_le_of_finrank_eq hdirectionCoord
    omega
  have hspanCoeff :
      (affineSpan ℝ F : Set (Fin n → ℝ)) ⊆
        {x | c ⬝ᵥ x = cover_inequality_rhs (theorem_7_4_cover (n := n) t)} := by
    apply affineSpan_subset_hyperplane_of_subset
    intro x hx
    have hxFace : x ∈ face_set P c
        (cover_inequality_rhs (theorem_7_4_cover (n := n) t)) := by
      simpa [F, lifted_cover_face, c] using hx
    exact (mem_face_set_iff.mp hxFace).2
  have hdirectionCoeff :
      (affineSpan ℝ F).direction ≤
        LinearMap.ker (dotProductStrongDual c).toLinearMap := by
    intro v hv
    rw [LinearMap.mem_ker]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀span] at hv
    rcases hv with ⟨x, hxspan, rfl⟩
    have hxEq := hspanCoeff hxspan
    have hx₀Eq := hspanCoeff hx₀span
    change c ⬝ᵥ x = cover_inequality_rhs (theorem_7_4_cover (n := n) t) at hxEq
    change c ⬝ᵥ x₀ = cover_inequality_rhs (theorem_7_4_cover (n := n) t) at hx₀Eq
    simp [dotProductStrongDual_apply, vsub_eq_sub, hxEq, hx₀Eq]
  have hcoverCard : 2 ≤ (theorem_7_4_cover (n := n) t).card :=
    cover_card_ge_two weights capacity hweights_le _ hC.toIsKnapsackCover
  have hcoverCardPos : 0 < (theorem_7_4_cover (n := n) t).card := by omega
  obtain ⟨i, hi⟩ : (theorem_7_4_cover (n := n) t).Nonempty := by
    exact Finset.card_pos.mp hcoverCardPos
  have hbasisCoordKer :
      Pi.single i (1 : ℝ) ∈
        LinearMap.ker (dotProductStrongDual (Pi.single j (1 : ℝ))).toLinearMap := by
    rw [LinearMap.mem_ker]
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hj hi
    simp [dotProductStrongDual_apply, dotProduct, Pi.single_apply, hij]
  have hbasisDirection : Pi.single i (1 : ℝ) ∈ (affineSpan ℝ F).direction := by
    rw [hdirectionEq]
    exact hbasisCoordKer
  have hbasisCoeffKer :
      Pi.single i (1 : ℝ) ∈ LinearMap.ker (dotProductStrongDual c).toLinearMap :=
    hdirectionCoeff hbasisDirection
  have hciZero : c i = 0 := by
    have hzero := LinearMap.mem_ker.mp hbasisCoeffKer
    simpa [dotProductStrongDual_apply, dotProduct, Pi.single_apply] using hzero
  have hciOne : c i = 1 := by
    simp [c, hi]
  -- A cover coordinate cannot simultaneously have coefficient zero and coefficient one.
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a coefficient vector already
normalized to one on its cover is fixed by `lifted_cover_inequality_coeff`. -/
private theorem theorem_7_4_liftedCoeff_eq_self_of_cover
    (C : Finset (Fin n))
    (α : Fin n → ℝ)
    (hα : ∀ i ∈ C, α i = 1) :
    lifted_cover_inequality_coeff C α = α := by
  -- Split on cover membership, where normalization is either the hypothesis or definitional.
  funext i
  by_cases hi : i ∈ C
  · simp [lifted_cover_inequality_coeff, hi, hα i hi]
  · simp [lifted_cover_inequality_coeff, hi]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: every binary knapsack point
belongs to the ambient zero-one point set used in Proposition 7.2. -/
private theorem theorem_7_4_knapsackSet_subset_zeroOnePoints
    (weights : Fin n → ℕ)
    (capacity : ℕ) :
    zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ⊆
      zero_one_points (Nat.le_refl n) (Set.univ : Set (Fin n → ℝ)) := by
  intro x hx
  rw [mem_zero_one_points_iff]
  rw [mem_zero_one_knapsack_set_iff] at hx
  exact ⟨Set.mem_univ x, hx.1⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: validity on a prefix knapsack
problem transfers to the zero slice after appending one coordinate. -/
private theorem theorem_7_4_lastCoordinateZeroSliceValid
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (α : Fin m → ℝ)
    (β : ℝ)
    (hvalid :
      is_valid_inequality
        (zero_one_knapsack_set (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ))
        α
        β) :
    is_valid_inequality
      (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
        last_coordinate_eq_set m 0)
      (Fin.snoc α 0)
      β := by
  intro x hx
  rcases hx with ⟨hxS, hxlast⟩
  have hxlast0 : x (Fin.last m) = 0 := mem_last_coordinate_eq_set_iff.mp hxlast
  have hy_mem :
      (fun i : Fin m ↦ x i.castSucc) ∈
        zero_one_knapsack_set (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ) := by
    rw [mem_zero_one_knapsack_set_iff] at hxS ⊢
    constructor
    · intro i
      simpa using hxS.1 i.castSucc
    · simpa [Fin.sum_univ_castSucc, hxlast0] using hxS.2
  have hy_valid := hvalid hy_mem
  -- The appended coefficient and coordinate both vanish on the zero slice.
  calc
    Fin.snoc α 0 ⬝ᵥ x = partial_lifting_value α x + 0 * x (Fin.last m) := by
      rw [dotProduct_last_coordinate_lifting_coeffs]
    _ = α ⬝ᵥ (fun i : Fin m ↦ x i.castSucc) := by
      simp [partial_lifting_value, dotProduct, hxlast0]
    _ ≤ β := hy_valid

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the singleton at a newly
appended coordinate is feasible when every individual item fits. -/
private theorem theorem_7_4_lastSingletonFeasible
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (hweights_le : ∀ i, weights i ≤ capacity) :
    Pi.single (Fin.last m) (1 : ℝ) ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    by_cases hi : i = Fin.last m
    · right
      subst i
      simp
    · left
      simp [hi]
  · let x : Fin (m + 1) → ℝ := Pi.single (Fin.last m) (1 : ℝ)
    have hsum :
        ∑ i, (weights i : ℝ) * (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) i =
          weights (Fin.last m) := by
      calc
        ∑ i, (weights i : ℝ) * (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) i =
            (fun i ↦ (weights i : ℝ)) ⬝ᵥ x := by
              simp [dotProduct, x]
        _ = weights (Fin.last m) * 1 := by simp [x]
        _ = weights (Fin.last m) := by ring
    rw [hsum]
    exact_mod_cast hweights_le (Fin.last m)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: appending a zero coordinate
preserves addition. -/
private theorem theorem_7_4_snocZero_add
    {m : ℕ}
    (x y : Fin m → ℝ) :
    (Fin.snoc (x + y) (0 : ℝ) : Fin (m + 1) → ℝ) =
      Fin.snoc x 0 + Fin.snoc y 0 := by
  -- Check inherited coordinates and the appended coordinate separately.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: appending a zero coordinate
preserves real scalar multiplication. -/
private theorem theorem_7_4_snocZero_smul
    {m : ℕ}
    (a : ℝ)
    (x : Fin m → ℝ) :
    (Fin.snoc (a • x) (0 : ℝ) : Fin (m + 1) → ℝ) = a • Fin.snoc x 0 := by
  -- Check inherited coordinates and the appended coordinate separately.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the linear zero-coordinate
embedding used to compare consecutive prefix stages. -/
private def theorem_7_4_snocZeroLinear (m : ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun := fun x ↦ Fin.snoc x 0
  map_add' := theorem_7_4_snocZero_add
  map_smul' := theorem_7_4_snocZero_smul

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the zero-coordinate embedding
evaluates to `Fin.snoc x 0`. -/
@[simp] private theorem theorem_7_4_snocZeroLinear_apply
    {m : ℕ}
    (x : Fin m → ℝ) :
    theorem_7_4_snocZeroLinear m x = Fin.snoc x 0 := by
  -- This is the defining computation rule of the embedding.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the zero-coordinate embedding
is injective. -/
private theorem theorem_7_4_snocZeroLinear_injective
    {m : ℕ} :
    Function.Injective (theorem_7_4_snocZeroLinear m) := by
  intro x y hxy
  funext i
  have hcoord := congrFun hxy i.castSucc
  simpa using hcoord

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a tight point of the previous
prefix face remains tight in the next zero-coordinate slice. -/
private theorem theorem_7_4_snocZero_mem_zeroSliceFace
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (α : Fin m → ℝ)
    (β : ℝ)
    {y : Fin m → ℝ}
    (hy :
      y ∈ face_set
        (zero_one_knapsack_polytope
          (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ))
        α β) :
    Fin.snoc y 0 ∈
      face_set
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
          last_coordinate_eq_set m 0)
        (Fin.snoc α 0) β := by
  let oldSet :=
    zero_one_knapsack_set (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ)
  let currentSet := zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let L := theorem_7_4_snocZeroLinear m
  have hsetImage : L '' oldSet ⊆ currentSet := by
    rintro z ⟨x, hx, rfl⟩
    rw [mem_zero_one_knapsack_set_iff] at hx ⊢
    constructor
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa [L] using hx.1 j
      · simp [L]
    · simpa [L, Fin.sum_univ_castSucc] using hx.2
  have hyData := mem_face_set_iff.mp hy
  have hyOldHull : y ∈ convexHull ℝ oldSet := by
    simpa [oldSet, zero_one_knapsack_polytope_eq_convexHull] using hyData.1
  have hyImageHull : L y ∈ convexHull ℝ (L '' oldSet) := by
    rw [← L.image_convexHull]
    exact ⟨y, hyOldHull, rfl⟩
  have hyCurrentHull : Fin.snoc y 0 ∈ convexHull ℝ currentSet := by
    have hmono := convexHull_mono hsetImage hyImageHull
    simpa [L] using hmono
  have hlastZero :
      (Fin.snoc y (0 : ℝ) : Fin (m + 1) → ℝ) (Fin.last m) = 0 := by
    simp
  rw [mem_face_set_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [currentSet, zero_one_knapsack_polytope_eq_convexHull] using hyCurrentHull
  · exact mem_last_coordinate_eq_set_iff.mpr hlastZero
  · simpa [dotProduct_last_coordinate_lifting_coeffs, partial_lifting_value, dotProduct,
      Fin.sum_univ_castSucc] using hyData.2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the zero-slice face at a
successor stage has dimension at least that of the preceding prefix face. -/
private theorem theorem_7_4_oldFace_finrank_le_zeroSliceFace
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (α : Fin m → ℝ)
    (β : ℝ) :
    Module.finrank ℝ
        (affineSpan ℝ
          (face_set
            (zero_one_knapsack_polytope
              (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ))
            α β)).direction ≤
      Module.finrank ℝ
        (affineSpan ℝ
          (face_set
            (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
              last_coordinate_eq_set m 0)
            (Fin.snoc α 0) β)).direction := by
  let oldFace : Set (Fin m → ℝ) :=
    face_set
      (zero_one_knapsack_polytope
        (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ)) α β
  let zeroSliceFace : Set (Fin (m + 1) → ℝ) :=
    face_set
      (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
        last_coordinate_eq_set m 0)
      (Fin.snoc α 0) β
  let L := theorem_7_4_snocZeroLinear m
  have himage : L '' oldFace ⊆ zeroSliceFace := by
    rintro z ⟨y, hy, rfl⟩
    exact theorem_7_4_snocZero_mem_zeroSliceFace weights capacity α β hy
  have hspan :
      affineSpan ℝ (L '' oldFace) = (affineSpan ℝ oldFace).map L.toAffineMap := by
    symm
    simpa using AffineSubspace.map_span L.toAffineMap oldFace
  have hmapRank :
      Module.finrank ℝ (affineSpan ℝ oldFace).direction =
        Module.finrank ℝ (affineSpan ℝ (L '' oldFace)).direction := by
    rw [hspan, AffineSubspace.map_direction]
    let e :
        (affineSpan ℝ oldFace).direction ≃ₗ[ℝ]
          Submodule.map L (affineSpan ℝ oldFace).direction :=
      Submodule.equivMapOfInjective
        L theorem_7_4_snocZeroLinear_injective (affineSpan ℝ oldFace).direction
    exact LinearEquiv.finrank_eq e
  have hdirection :
      (affineSpan ℝ (L '' oldFace)).direction ≤ (affineSpan ℝ zeroSliceFace).direction :=
    AffineSubspace.direction_le (affineSpan_mono ℝ himage)
  -- Injectivity preserves the old dimension, and affine-span monotonicity supplies the bound.
  calc
    Module.finrank ℝ (affineSpan ℝ oldFace).direction =
        Module.finrank ℝ (affineSpan ℝ (L '' oldFace)).direction := hmapRank
    _ ≤ Module.finrank ℝ (affineSpan ℝ zeroSliceFace).direction :=
      Submodule.finrank_mono hdirection

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a nonempty equality face
whose normal has a unit coordinate has codimension at least one. -/
private theorem theorem_7_4_faceSet_finrank_add_one_le
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {β : ℝ}
    (j : Fin n)
    (hcj : c j = 1)
    (hface : (face_set P c β).Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (face_set P c β)).direction + 1 ≤ n := by
  rcases hface with ⟨x₀, hx₀⟩
  have hsubset : face_set P c β ⊆ {x : Fin n → ℝ | c ⬝ᵥ x = β} := by
    intro x hx
    exact (mem_face_set_iff.mp hx).2
  have hspanSubset :
      (affineSpan ℝ (face_set P c β) : Set (Fin n → ℝ)) ⊆
        {x : Fin n → ℝ | c ⬝ᵥ x = β} :=
    affineSpan_subset_hyperplane_of_subset hsubset
  have hx₀span : x₀ ∈ affineSpan ℝ (face_set P c β) :=
    subset_affineSpan ℝ _ hx₀
  have hdirection :
      (affineSpan ℝ (face_set P c β)).direction ≤
        LinearMap.ker (dotProductStrongDual c).toLinearMap := by
    intro v hv
    rw [LinearMap.mem_ker]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀span] at hv
    rcases hv with ⟨x, hxspan, rfl⟩
    have hxEq : c ⬝ᵥ x = β := hspanSubset hxspan
    have hx₀Eq : c ⬝ᵥ x₀ = β := (mem_face_set_iff.mp hx₀).2
    simp [dotProductStrongDual_apply, vsub_eq_sub, hxEq, hx₀Eq]
  have hsurjective : Function.Surjective (dotProductStrongDual c).toLinearMap := by
    intro y
    refine ⟨y • Pi.single j (1 : ℝ), ?_⟩
    simp [dotProductStrongDual_apply, dotProduct, Pi.single_apply, hcj]
  have hrange : LinearMap.range (dotProductStrongDual c).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  have hrangeFinrank :
      Module.finrank ℝ (LinearMap.range (dotProductStrongDual c).toLinearMap) = 1 := by
    rw [hrange, finrank_top]
    simp
  have hrankNull := LinearMap.finrank_range_add_finrank_ker (dotProductStrongDual c).toLinearMap
  have hkernelFinrank :
      Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 = n := by
    rw [hrangeFinrank] at hrankNull
    simpa [Module.finrank_fintype_fun_eq_card, add_comm] using hrankNull
  calc
    Module.finrank ℝ (affineSpan ℝ (face_set P c β)).direction + 1 ≤
        Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 :=
      Nat.add_le_add_right (Submodule.finrank_mono hdirection) 1
    _ = n := hkernelFinrank

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a facet lifting on a prefix
knapsack problem extends by the maximal Proposition 7.2 coefficient to a facet lifting after one
new coordinate is appended. -/
private theorem theorem_7_4_existsSuccessorFacetLifting
    {m t : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (ht : t ≤ m)
    (htwo : 2 ≤ t)
    (hweights_le : ∀ i, weights i ≤ capacity)
    {α : Fin m → ℝ}
    (hα :
      α ∈ facet_defining_liftings_of_minimal_cover_inequality
        (fun i : Fin m ↦ weights i.castSucc) capacity (theorem_7_4_cover t)) :
    ∃ γ : ℝ,
      Fin.snoc α γ ∈ facet_defining_liftings_of_minimal_cover_inequality
        weights capacity (theorem_7_4_cover t) ∧
      IsGreatest
        (valid_last_coordinate_lifting_coefficients
          (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)) α
          (cover_inequality_rhs (theorem_7_4_cover (n := m + 1) t)))
        γ := by
  let S := zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let P := convexHull ℝ S
  let oldP :=
    zero_one_knapsack_polytope
      (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ)
  let β := cover_inequality_rhs (theorem_7_4_cover (n := m + 1) t)
  let coeff := last_coordinate_lifting_coefficient S α β
  let oldFace : Set (Fin m → ℝ) := face_set oldP α β
  let zeroSliceFace : Set (Fin (m + 1) → ℝ) :=
    face_set (P ∩ last_coordinate_eq_set m 0) (Fin.snoc α 0) β
  let liftedFace : Set (Fin (m + 1) → ℝ) := face_set P (Fin.snoc α coeff) β
  have hαvalid := (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hα).1
  have hαcover : ∀ i ∈ theorem_7_4_cover t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).1
  have hαnorm : lifted_cover_inequality_coeff (theorem_7_4_cover t) α = α :=
    theorem_7_4_liftedCoeff_eq_self_of_cover _ _ hαcover
  have hbetaEq :
      cover_inequality_rhs (theorem_7_4_cover (n := m) t) = β := by
    -- Consecutive stages have the same `t` cover coordinates.
    simp [β, cover_inequality_rhs_eq,
      theorem_7_4_cover_card (n := m) t ht,
      theorem_7_4_cover_card (n := m + 1) t (Nat.le_trans ht (Nat.le_succ m))]
  have hfacetOldRaw :=
    (mem_facet_defining_liftings_of_cover_inequality_iff.mp
      (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hα).2)
  rw [lifted_cover_face, hαnorm] at hfacetOldRaw
  have hfacetOld : IsFacetOf oldP oldFace := by
    simpa [oldP, oldFace, hbetaEq] using hfacetOldRaw
  rcases isFacetOf_iff.mp hfacetOld with ⟨holdNonempty, -, holdCodim⟩
  have holdOverweight :
      zero_one_knapsack_overweight_indices
          (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ) = ∅ := by
    ext i
    simp [zero_one_knapsack_overweight_indices, hweights_le i.castSucc]
  have holdDim : Module.finrank ℝ (affineSpan ℝ oldP).direction = m := by
    have hnonnegative : ∀ i : Fin m, 0 ≤ (weights i.castSucc : ℝ) := by
      intro i
      positivity
    have hcapacityNonnegative : (0 : ℝ) ≤ capacity := by positivity
    simpa [oldP, holdOverweight] using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        (fun i : Fin m ↦ (weights i.castSucc : ℝ))
        (capacity : ℝ) hnonnegative hcapacityNonnegative
  have holdFaceDim : Module.finrank ℝ (affineSpan ℝ oldFace).direction + 1 = m := by
    rw [holdCodim, holdDim]
  have hzeroSliceNonempty : zeroSliceFace.Nonempty := by
    rcases holdNonempty with ⟨y, hy⟩
    refine ⟨Fin.snoc y 0, ?_⟩
    simpa [zeroSliceFace, P, S, oldFace, oldP, zero_one_knapsack_polytope_eq_convexHull] using
      theorem_7_4_snocZero_mem_zeroSliceFace weights capacity α β hy
  have holdDimLeZeroSliceDim :
      Module.finrank ℝ (affineSpan ℝ oldFace).direction ≤
        Module.finrank ℝ (affineSpan ℝ zeroSliceFace).direction := by
    simpa [zeroSliceFace, P, S, oldFace, oldP, zero_one_knapsack_polytope_eq_convexHull] using
      theorem_7_4_oldFace_finrank_le_zeroSliceFace weights capacity α β
  have hvalidPrevPoly :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hαvalid).2
  have hvalidPrevSet :
      is_valid_inequality
        (zero_one_knapsack_set
          (fun i : Fin m ↦ (weights i.castSucc : ℝ)) (capacity : ℝ)) α β := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hvalidPrevPoly
    simpa [hbetaEq] using is_valid_inequality_convexHull_iff.mp hvalidPrevPoly
  have hvalidZero :
      is_valid_inequality (S ∩ last_coordinate_eq_set m 0) (Fin.snoc α 0) β := by
    exact theorem_7_4_lastCoordinateZeroSliceValid weights capacity α β hvalidPrevSet
  have hSBinary :
      S ⊆ zero_one_points (Nat.le_refl (m + 1)) (Set.univ : Set (Fin (m + 1) → ℝ)) := by
    simpa [S] using theorem_7_4_knapsackSet_subset_zeroOnePoints weights capacity
  have hlastSingletonValue :
      (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) (Fin.last m) = 1 := by
    simp
  have honeSliceNonempty : Set.Nonempty (S ∩ last_coordinate_eq_set m 1) := by
    refine ⟨Pi.single (Fin.last m) (1 : ℝ), ?_⟩
    refine ⟨?_, mem_last_coordinate_eq_set_iff.mpr hlastSingletonValue⟩
    simpa [S] using theorem_7_4_lastSingletonFeasible weights capacity hweights_le
  have hvalidSet : is_valid_inequality S (Fin.snoc α coeff) β := by
    exact binary_last_coordinate_lifting_is_valid S α β hSBinary hvalidZero honeSliceNonempty
  let d := Module.finrank ℝ (affineSpan ℝ zeroSliceFace).direction
  have hzeroSliceDim :
      Module.finrank ℝ
          (affineSpan ℝ
            (face_set (convexHull ℝ S ∩ last_coordinate_eq_set m 0)
              (Fin.snoc α 0) β)).direction = d := by
    rfl
  have hzeroSliceNonemptyForStep :
      Set.Nonempty
        (face_set (convexHull ℝ S ∩ last_coordinate_eq_set m 0)
          (Fin.snoc α 0) β) := by
    simpa [zeroSliceFace, P] using hzeroSliceNonempty
  have hdimensionStep :=
    binary_last_coordinate_lifting_face_dimension_lower_bound
      S α β d hSBinary hvalidZero honeSliceNonempty
      hzeroSliceNonemptyForStep hzeroSliceDim
  have hliftedExposed : IsExposed ℝ P liftedFace := by
    simpa [P, liftedFace, coeff] using hdimensionStep.1
  have hliftedDimLower : m ≤ Module.finrank ℝ (affineSpan ℝ liftedFace).direction := by
    -- The old facet contributes `m - 1` directions, and lifting adds one more.
    have hstepDim :
        d + 1 ≤ Module.finrank ℝ (affineSpan ℝ liftedFace).direction := by
      simpa [P, liftedFace, coeff] using hdimensionStep.2
    dsimp [d] at hstepDim
    omega
  have htPositive : 0 < t := by omega
  have hmPositive : 0 < m := lt_of_lt_of_le htPositive ht
  have hliftedNonempty : liftedFace.Nonempty := by
    by_contra hnot
    have hempty : liftedFace = ∅ := Set.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty, AffineSubspace.span_empty, AffineSubspace.direction_bot,
      finrank_bot] at hliftedDimLower
    omega
  have hnextCover :
      ∀ i ∈ theorem_7_4_cover t, (Fin.snoc α coeff : Fin (m + 1) → ℝ) i = 1 := by
    intro i hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · have hklt : k < t := by
        simpa using theorem_7_4_cover_mem_iff.mp hi
      simpa using hαcover k (theorem_7_4_cover_mem_iff.mpr hklt)
    · exact False.elim (Nat.not_lt_of_ge ht (theorem_7_4_cover_mem_iff.mp hi))
  have hnextNorm :
      lifted_cover_inequality_coeff (theorem_7_4_cover t) (Fin.snoc α coeff) =
        Fin.snoc α coeff :=
    theorem_7_4_liftedCoeff_eq_self_of_cover _ _ hnextCover
  have hzeroMem : (0 : Fin (m + 1)) ∈ theorem_7_4_cover t := by
    exact theorem_7_4_cover_mem_iff.mpr htPositive
  have hzeroCoeff :
      (Fin.snoc α coeff : Fin (m + 1) → ℝ) (0 : Fin (m + 1)) = 1 :=
    hnextCover 0 hzeroMem
  have hliftedDimUpper :
      Module.finrank ℝ (affineSpan ℝ liftedFace).direction + 1 ≤ m + 1 := by
    simpa [liftedFace, P] using
      theorem_7_4_faceSet_finrank_add_one_le 0 hzeroCoeff hliftedNonempty
  have hliftedDim : Module.finrank ℝ (affineSpan ℝ liftedFace).direction = m := by
    omega
  have hcurrentOverweight :
      zero_one_knapsack_overweight_indices
          (fun i ↦ (weights i : ℝ)) (capacity : ℝ) = ∅ := by
    ext i
    simp [zero_one_knapsack_overweight_indices, hweights_le i]
  have hpolytopeDim : Module.finrank ℝ (affineSpan ℝ P).direction = m + 1 := by
    have hnonnegative : ∀ i, 0 ≤ (weights i : ℝ) := by
      intro i
      positivity
    have hcapacityNonnegative : (0 : ℝ) ≤ capacity := by positivity
    simpa [P, S, zero_one_knapsack_polytope_eq_convexHull, hcurrentOverweight] using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        (fun i ↦ (weights i : ℝ)) (capacity : ℝ) hnonnegative hcapacityNonnegative
  have hliftedCodim :
      Module.finrank ℝ (affineSpan ℝ liftedFace).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ P).direction := by
    rw [hliftedDim, hpolytopeDim]
  have hvalidPoly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Fin.snoc α coeff) β := by
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hvalidSet
  refine ⟨coeff, ?_, ?_⟩
  · rw [mem_facet_defining_liftings_of_minimal_cover_inequality_iff]
    constructor
    · exact (mem_valid_liftings_of_minimal_cover_inequality_iff.mpr ⟨hnextCover, hvalidPoly⟩)
    · rw [mem_facet_defining_liftings_of_cover_inequality_iff, lifted_cover_face, hnextNorm]
      simpa [P, S, liftedFace, β, zero_one_knapsack_polytope_eq_convexHull] using
        (isFacetOf_iff.mpr ⟨hliftedNonempty, hliftedExposed, hliftedCodim⟩)
  · simpa [S, β, coeff] using
      binary_last_coordinate_lifting_maximal S α β hSBinary hvalidZero honeSliceNonempty

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: iterating maximal
last-coordinate lifts extends a prefix facet while preserving every coefficient already present. -/
private theorem theorem_7_4_existsFacetLiftingExtension
    (m r t : ℕ)
    (ht : t ≤ m)
    (htwo : 2 ≤ t)
    (weights : Fin (m + r) → ℕ)
    (capacity : ℕ)
    (hweights_le : ∀ i, weights i ≤ capacity)
    (α : Fin m → ℝ)
    (hα :
      α ∈ facet_defining_liftings_of_minimal_cover_inequality
        (fun i : Fin m ↦ weights (i.castLE (Nat.le_add_right m r)))
        capacity
        (theorem_7_4_cover t)) :
    ∃ extendedCoeff : Fin (m + r) → ℝ,
      extendedCoeff ∈ facet_defining_liftings_of_minimal_cover_inequality
        weights capacity (theorem_7_4_cover t) ∧
      ∀ i : Fin m, extendedCoeff (i.castLE (Nat.le_add_right m r)) = α i := by
  induction r with
  | zero =>
      -- With no new coordinates, the given facet and its coefficients are unchanged.
      refine ⟨α, ?_, ?_⟩
      · simpa using hα
      · intro i
        rfl
  | succ r ih =>
      let previousWeights : Fin (m + r) → ℕ := fun i ↦ weights i.castSucc
      have hpreviousWeights_le : ∀ i, previousWeights i ≤ capacity := by
        intro i
        exact hweights_le i.castSucc
      have hαPrevious :
          α ∈ facet_defining_liftings_of_minimal_cover_inequality
            (fun i : Fin m ↦ previousWeights (i.castLE (Nat.le_add_right m r)))
            capacity
            (theorem_7_4_cover t) := by
        simpa [previousWeights] using hα
      obtain ⟨αPrevious, hfacetPrevious, hpreservedPrevious⟩ :=
        ih previousWeights hpreviousWeights_le hαPrevious
      obtain ⟨γ, hfacetCurrent, -⟩ :=
        theorem_7_4_existsSuccessorFacetLifting
          weights capacity (Nat.le_trans ht (Nat.le_add_right m r)) htwo hweights_le hfacetPrevious
      refine ⟨Fin.snoc αPrevious γ, hfacetCurrent, ?_⟩
      intro i
      -- `Fin.snoc` agrees with the previous vector on every inherited prefix coordinate.
      have hindex :
          i.castLE (Nat.le_add_right m (Nat.succ r)) =
            (i.castLE (Nat.le_add_right m r)).castSucc := by
        exact Fin.ext rfl
      have hsnoc :
          (Fin.snoc αPrevious γ : Fin ((m + r) + 1) → ℝ)
              ((i.castLE (Nat.le_add_right m r)).castSucc) =
            αPrevious (i.castLE (Nat.le_add_right m r)) := by
        rw [Fin.snoc_castSucc]
      calc
        (Fin.snoc αPrevious γ : Fin (m + Nat.succ r) → ℝ)
              (i.castLE (Nat.le_add_right m (Nat.succ r))) =
            (Fin.snoc αPrevious γ : Fin ((m + r) + 1) → ℝ)
              ((i.castLE (Nat.le_add_right m r)).castSucc) :=
          congrArg (Fin.snoc αPrevious γ) hindex
        _ = αPrevious (i.castLE (Nat.le_add_right m r)) := hsnoc
        _ = α i := hpreservedPrevious i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: deleting an off-cover last
coordinate identifies the current prefix cover with the `Fin.castSucc` image of the old cover. -/
private theorem theorem_7_4_cover_eq_castSuccImage
    {m t : ℕ}
    (ht : t ≤ m) :
    theorem_7_4_cover (n := m + 1) t =
      (theorem_7_4_cover (n := m) t).map Fin.castSuccEmb := by
  -- Split a current coordinate into an inherited coordinate or the new last coordinate.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [theorem_7_4_cover_mem_iff]
  · simp [theorem_7_4_cover, Nat.not_lt.mpr ht]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: erasing a prefix coordinate
commutes with the `Fin.castSucc` image. -/
private theorem theorem_7_4_cover_erase_eq_castSuccImage
    {m t : ℕ}
    (ht : t ≤ m)
    {j : Fin m} :
    ((theorem_7_4_cover (n := m) t).erase j).map Fin.castSuccEmb =
      (theorem_7_4_cover (n := m + 1) t).erase j.castSucc := by
  -- Again separate inherited coordinates from the off-cover last coordinate.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · simp [theorem_7_4_cover_mem_iff]
  · simp [theorem_7_4_cover, Nat.not_lt.mpr ht]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: prefix-cover sums are unchanged
when an off-cover last coordinate is deleted. -/
private theorem theorem_7_4_coverSum_castSucc_eq
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ) :
    (theorem_7_4_cover (n := m) t).sum (fun i : Fin m ↦ weights i.castSucc) =
      (theorem_7_4_cover (n := m + 1) t).sum weights := by
  -- Reindex the finite sum by the canonical embedding.
  rw [theorem_7_4_cover_eq_castSuccImage ht, Finset.sum_map]
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: erased prefix-cover sums are
unchanged when an off-cover last coordinate is deleted. -/
private theorem theorem_7_4_coverEraseSum_castSucc_eq
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    {j : Fin m} :
    ((theorem_7_4_cover (n := m + 1) t).erase j.castSucc).sum weights =
      ((theorem_7_4_cover (n := m) t).erase j).sum
        (fun i : Fin m ↦ weights i.castSucc) := by
  -- Transport erasure through the same `Fin.castSucc` embedding before summing.
  rw [← theorem_7_4_cover_erase_eq_castSuccImage (m := m) (t := t) ht (j := j),
    Finset.sum_map]
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: minimality of a prefix cover
survives deletion of an off-cover last coordinate. -/
private theorem theorem_7_4_minimalCover_castSucc
    {m t : ℕ}
    (capacity : ℕ)
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t)) :
    IsMinimalKnapsackCover
      (fun i : Fin m ↦ weights i.castSucc) capacity (theorem_7_4_cover t) := by
  refine (isMinimalKnapsackCover_iff _ _ _).mpr ?_
  constructor
  · rw [isKnapsackCover_iff]
    have hcover :=
      (isKnapsackCover_iff weights capacity (theorem_7_4_cover t)).mp hC.toIsKnapsackCover
    rw [theorem_7_4_coverSum_castSucc_eq ht weights]
    exact hcover
  · intro j hj
    have hjCurrent : j.castSucc ∈ theorem_7_4_cover (n := m + 1) t := by
      simpa [theorem_7_4_cover_mem_iff] using hj
    have herase := hC.erase_sum_le j.castSucc hjCurrent
    simpa [theorem_7_4_coverEraseSum_castSucc_eq ht weights (j := j)] using herase

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: restricting a prefix minimal
cover across any finite suffix preserves its minimal-cover property. -/
private theorem theorem_7_4_minimalCover_castLE
    (m r t : ℕ)
    (ht : t ≤ m)
    (weights : Fin (m + r) → ℕ)
    (capacity : ℕ)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t)) :
    IsMinimalKnapsackCover
      (fun i : Fin m ↦ weights (i.castLE (Nat.le_add_right m r)))
      capacity
      (theorem_7_4_cover t) := by
  induction r with
  | zero =>
      -- Restriction across an empty suffix is the original minimal cover.
      simpa using hC
  | succ r ih =>
      let previousWeights : Fin (m + r) → ℕ := fun i ↦ weights i.castSucc
      have hpreviousCover :
          IsMinimalKnapsackCover
            previousWeights capacity (theorem_7_4_cover t) :=
        theorem_7_4_minimalCover_castSucc
          capacity (Nat.le_trans ht (Nat.le_add_right m r)) weights hC
      have hrestricted := ih previousWeights hpreviousCover
      -- Composing the last-coordinate deletion with the prefix embedding is `Fin.castLE`.
      simpa [previousWeights] using hrestricted

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: on binary coordinates, the
sum over a finite set is its cardinality minus the number of zero coordinates. -/
private theorem theorem_7_4_sum_binary_eq_card_sub_zeros
    (C : Finset (Fin n))
    (x : Fin n → ℝ)
    (hbinary : ∀ i ∈ C, x i = 0 ∨ x i = 1) :
    C.sum x =
      ((C.card - (C.filter (fun i ↦ x i = 0)).card : ℕ) : ℝ) := by
  classical
  let Z := C.filter fun i ↦ x i = 0
  have hsumIndicator :
      C.sum x = C.sum (fun i ↦ if i ∈ Z then (0 : ℝ) else 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiZ : i ∈ Z
    · have hxi : x i = 0 := (Finset.mem_filter.mp hiZ).2
      simp [hiZ, hxi]
    · have hxi : x i = 1 := by
        rcases hbinary i hi with hzero | hone
        · exact False.elim (hiZ (Finset.mem_filter.mpr ⟨hi, hzero⟩))
        · exact hone
      simp [hiZ, hxi]
  have hfilter : C.filter (fun i ↦ i ∉ Z) = C \ Z := by
    ext i
    simp
  have hZsubset : Z ⊆ C := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  rw [hsumIndicator]
  calc
    C.sum (fun i ↦ if i ∈ Z then (0 : ℝ) else 1) =
        C.sum (fun i ↦ if i ∉ Z then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiZ : i ∈ Z
      · simp [hiZ]
      · simp [hiZ]
    _ =
        ((C.filter (fun i ↦ i ∉ Z)).card : ℝ) := by
      simpa using (Finset.sum_boole (R := ℝ) (fun i ↦ i ∉ Z) C)
    _ = ((C \ Z).card : ℝ) := by rw [hfilter]
    _ = ((C.card - Z.card : ℕ) : ℝ) := by rw [Finset.card_sdiff_of_subset hZsubset]
    _ = ((C.card - (C.filter (fun i ↦ x i = 0)).card : ℕ) : ℝ) := by rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean
— Theorem 7.4 (1). Let
`K := {x ∈ {0,1}^n | ∑ j, a_j x_j ≤ b}`, assume `b ≥ a_j > 0` for all `j`, let
`C = {1, ..., t}` be a minimal cover with ordered cover weights `a₁ ≥ a₂ ≥ ··· ≥ a_t`, and let
`∑_{j ∈ C} x_j + ∑_{j ∉ C} α_j x_j ≤ |C| - 1` be a facet-defining lifting of the cover
inequality. If `μ_h ≤ a_j ≤ μ_{h+1} - λ` for some `j ∉ C` and `h < t`, then `α_j = h`. -/
theorem theorem_7_4_forces_exact_lifting_coefficient
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hordered : theorem_7_4_cover_weights_descending weights ht)
    {α : Fin n → ℝ}
    (hαfacet : α ∈ theorem_7_4_facet_defining_liftings weights capacity t)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_exact_interval_condition weights capacity t ht j h) :
    α j = h :=
  by
  have hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t) :=
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hαfacet).1
  have hupper : α j ≤ h := by
    -- The exact interval already supplies the source upper bound.
    exact theorem_7_4_exact_interval_upper_bound weights capacity t ht hC hαvalid hj hh hinterval
  have hlower : (h : ℝ) ≤ α j := by
    -- Exchange validity and facet maximality force coefficient `h` below `α j`.
    apply validUpdate_le_facetCoefficient weights capacity t hweights_le hC hαfacet hj
    exact
      validCoefficientUpdateOfMuLeWeight
        weights capacity t ht hC hordered hαvalid hj hinterval.1
  -- The matching source bounds determine the coefficient exactly.
  by_cases hjpos : 0 < weights j
  · exact le_antisymm hupper hlower
  · exact False.elim (hjpos (hweights_pos j))

/-- Theorem 7.4 (2). Under the same hypotheses as Theorem 7.4, if
`μ_{h+1} - λ < a_j < μ_{h+1}` for some `j ∉ C` and `h < t`, then the lifting coefficient lies in
the interval `h ≤ α_j ≤ h + 1`. -/
theorem theorem_7_4_bounds_lifting_coefficient_on_boundary_interval
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hordered : theorem_7_4_cover_weights_descending weights ht)
    {α : Fin n → ℝ}
    (hαfacet : α ∈ theorem_7_4_facet_defining_liftings weights capacity t)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_boundary_interval_condition weights capacity t ht j h) :
    (h : ℝ) ≤ α j ∧ α j ≤ h + 1 :=
  by
  have hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity (theorem_7_4_cover t) :=
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hαfacet).1
  have hupper : α j ≤ h + 1 := by
    -- The shifted suffix witness gives the source upper bound on the boundary interval.
    exact
      theorem_7_4_boundary_interval_upper_bound
        weights capacity t ht hweights_le hC hαvalid hj hh hinterval
  have hlam_le :
      theorem_7_4_cover_excess weights capacity t ht ≤
        theorem_7_4_cover_weight weights ht ⟨h, hh⟩ := by
    -- Minimality bounds the cover excess by every cover weight, in particular the next summand.
    exact theorem_7_4_coverExcess_le_coverWeight weights capacity t ht hC ⟨h, hh⟩
  have hmu_le_lower :
      theorem_7_4_mu weights t ht h ≤
        theorem_7_4_mu weights t ht (h + 1) -
          theorem_7_4_cover_excess weights capacity t ht := by
    -- Expand `μ_(h+1)` and cancel the excess using the preceding minimal-cover bound.
    rw [theorem_7_4_mu_succ_of_lt weights t ht h hh]
    omega
  have hmu_le_weight : theorem_7_4_mu weights t ht h ≤ weights j := by
    -- The open lower boundary places the item strictly above this admissible prefix sum.
    exact le_trans hmu_le_lower (Nat.le_of_lt hinterval.1)
  have hlower : (h : ℝ) ≤ α j := by
    -- Reuse the exchange validity and facet-maximality bridge from part (1).
    apply validUpdate_le_facetCoefficient weights capacity t hweights_le hC hαfacet hj
    exact
      validCoefficientUpdateOfMuLeWeight
        weights capacity t ht hC hordered hαvalid hj hmu_le_weight
  -- The two independent witness bounds give the claimed closed interval.
  by_cases hjpos : 0 < weights j
  · exact ⟨hlower, hupper⟩
  · exact False.elim (hjpos (hweights_pos j))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: when the prefix cover is the
whole coordinate set, its normalized cover coefficient cuts out a facet of the knapsack polytope. -/
private theorem theorem_7_4_univCoverFacetLifting
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (hweights_le : ∀ i, weights i ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover n)) :
    (fun _ : Fin n ↦ (1 : ℝ)) ∈
      facet_defining_liftings_of_minimal_cover_inequality
        weights capacity (theorem_7_4_cover n) := by
  have hnTwo : 2 ≤ n := by
    simpa [theorem_7_4_cover_card (n := n) n (Nat.le_refl n)] using
      cover_card_ge_two weights capacity hweights_le _ hC.toIsKnapsackCover
  have hnPositive : 0 < n := by omega
  rcases Nat.exists_eq_succ_of_ne_zero hnPositive.ne' with ⟨m, rfl⟩
  let C := theorem_7_4_cover (n := m + 1) (m + 1)
  let coeff : Fin (m + 1) → ℝ := cover_indicator C
  let P := zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let F := face_set P coeff (cover_inequality_rhs C)
  have hCUniv : C = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact theorem_7_4_cover_mem_iff.mpr i.isLt
  have honesEq : (fun _ : Fin (m + 1) ↦ (1 : ℝ)) = coeff := by
    funext i
    simp [coeff, C, hCUniv, cover_indicator]
  have hvalidHull : is_valid_inequality P coeff (cover_inequality_rhs C) := by
    simpa [P, coeff, C] using
      coverInequality_validOnKnapsackPolytope
        weights capacity (theorem_7_4_cover (m + 1)) hC.toIsKnapsackCover
  have hpMem : ∀ i : Fin (m + 1), omitPoint C i ∈ F := by
    intro i
    have hi : i ∈ C := by simp [hCUniv]
    rw [mem_face_set_iff]
    constructor
    · simpa [P] using
        subset_convexHull ℝ
          (zero_one_knapsack_set (fun k ↦ (weights k : ℝ)) (capacity : ℝ))
          (omitPoint_mem_zeroOneKnapsackSet weights capacity C hC hi)
    · simpa [coeff, coverIndicator_dot_eq_sum] using omitPoint_coverSum_eq_rhs C hi
  let p : Fin (m + 1) → Fin (m + 1) → ℝ := fun i ↦ omitPoint C i
  have hpAffine : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_linearIndependent_tail_sub p, Fintype.linearIndependent_iff]
    intro g hg i
    have hcoord := congrArg (fun x : Fin (m + 1) → ℝ ↦ x i.succ) hg
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, omitPoint, Finset.mem_erase,
      ne_eq, Fin.succ_inj, theorem_7_4_cover_mem_iff, Fin.val_succ, Order.lt_add_one_iff,
      Order.add_one_le_iff, Fin.is_lt, and_true, ite_not, Fin.succ_ne_zero, not_false_eq_true,
      and_self, ↓reduceIte, smul_eq_mul, Pi.zero_apply, p, C] at hcoord
    rw [Fintype.sum_eq_single i] at hcoord
    · simpa using hcoord
    · intro j hji
      simp [Ne.symm hji]
  have hFNonempty : F.Nonempty := ⟨p 0, hpMem 0⟩
  have hFExposed : IsExposed ℝ P F := by
    simpa [F, P] using isExposed_face_set_of_valid_inequality hvalidHull
  have hdimLower : m ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    let u : Fin m → Fin (m + 1) → ℝ := fun i ↦ p i.succ - p 0
    have huDirection : ∀ i : Fin m, u i ∈ (affineSpan ℝ F).direction := by
      intro i
      exact
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ F (hpMem i.succ))
          (subset_affineSpan ℝ F (hpMem 0))
    have hspanLe : Submodule.span ℝ (Set.range u) ≤ (affineSpan ℝ F).direction := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact huDirection i
    have huIndependent : LinearIndependent ℝ u := by
      simpa [u] using (affineIndependent_iff_linearIndependent_tail_sub p).mp hpAffine
    have hspanRank : Module.finrank ℝ (Submodule.span ℝ (Set.range u)) = m := by
      simpa [u] using finrank_span_eq_card (R := ℝ) (b := u) huIndependent
    simpa [hspanRank] using Submodule.finrank_mono hspanLe
  have hdimUpper : Module.finrank ℝ (affineSpan ℝ F).direction ≤ m := by
    have hcoeffZero : coeff 0 = 1 := by simp [coeff, C, cover_indicator]
    have hcodim := theorem_7_4_faceSet_finrank_add_one_le 0 hcoeffZero hFNonempty
    have hcodim' : Module.finrank ℝ (affineSpan ℝ F).direction + 1 ≤ m + 1 := by
      simpa [F] using hcodim
    omega
  have hFDim : Module.finrank ℝ (affineSpan ℝ F).direction = m :=
    le_antisymm hdimUpper hdimLower
  have hoverweight :
      zero_one_knapsack_overweight_indices
          (fun i ↦ (weights i : ℝ)) (capacity : ℝ) = ∅ := by
    ext i
    simp [zero_one_knapsack_overweight_indices, hweights_le i]
  have hPDim : Module.finrank ℝ (affineSpan ℝ P).direction = m + 1 := by
    have hnonnegative : ∀ i, 0 ≤ (weights i : ℝ) := by
      intro i
      positivity
    have hcapacityNonnegative : (0 : ℝ) ≤ capacity := by positivity
    simpa [P, hoverweight] using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        (fun i ↦ (weights i : ℝ)) (capacity : ℝ) hnonnegative hcapacityNonnegative
  have hFCodim :
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ P).direction := by
    rw [hFDim, hPDim]
  have hcoverOnes : ∀ i ∈ C, (fun _ : Fin (m + 1) ↦ (1 : ℝ)) i = 1 := by
    simp
  have hvalidOnes :
      is_valid_inequality P (fun _ : Fin (m + 1) ↦ (1 : ℝ)) (cover_inequality_rhs C) := by
    simpa [honesEq] using hvalidHull
  rw [mem_facet_defining_liftings_of_minimal_cover_inequality_iff]
  constructor
  · rw [mem_valid_liftings_of_minimal_cover_inequality_iff]
    have hvalidOriginal :
        is_valid_inequality
          (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
          (fun _ : Fin (m + 1) ↦ (1 : ℝ))
          (cover_inequality_rhs (theorem_7_4_cover (n := m + 1) (m + 1))) := by
      simpa [P, C] using hvalidOnes
    exact ⟨hcoverOnes, hvalidOriginal⟩
  · rw [mem_facet_defining_liftings_of_cover_inequality_iff, lifted_cover_face]
    have hnorm :
        lifted_cover_inequality_coeff C (fun _ : Fin (m + 1) ↦ (1 : ℝ)) =
          (fun _ : Fin (m + 1) ↦ (1 : ℝ)) :=
      theorem_7_4_liftedCoeff_eq_self_of_cover C _ hcoverOnes
    rw [hnorm]
    simpa [F, P, C, honesEq] using
      (isFacetOf_iff.mpr ⟨hFNonempty, hFExposed, hFCodim⟩)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: on the first stage consisting
of the prefix cover and one boundary item, `h + 1` is the greatest valid lifting coefficient. -/
private theorem boundaryFirstStageCoefficientIsGreatest
    (weights : Fin (t + 1) → ℕ)
    (capacity : ℕ)
    (hweights_le : ∀ i, weights i ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hdescending :
      theorem_7_4_cover_weights_descending weights (Nat.le_succ t))
    {h : ℕ}
    (hh : h < t)
    (hinterval :
      theorem_7_4_boundary_interval_condition
        weights capacity t (Nat.le_succ t) (Fin.last t) h) :
    IsGreatest
      (valid_last_coordinate_lifting_coefficients
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (fun _ : Fin t ↦ (1 : ℝ))
        (cover_inequality_rhs (theorem_7_4_cover (n := t + 1) t)))
      (h + 1 : ℝ) := by
  classical
  let C := theorem_7_4_cover (n := t + 1) t
  let S := zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let α : Fin t → ℝ := fun _ ↦ 1
  let β := cover_inequality_rhs C
  have hjLast : Fin.last t ∉ C := by
    simp [C, theorem_7_4_cover_mem_iff]
  have hCprev :
      IsMinimalKnapsackCover
        (fun i : Fin t ↦ weights i.castSucc) capacity (theorem_7_4_cover t) :=
    theorem_7_4_minimalCover_castSucc capacity (Nat.le_refl t) weights hC
  have hprevUniv : theorem_7_4_cover (n := t) t = Finset.univ := by
    ext i
    simp [theorem_7_4_cover_mem_iff]
  have hαeq : α = cover_indicator (theorem_7_4_cover (n := t) t) := by
    funext i
    simp [α, hprevUniv, cover_indicator]
  have hbetaEq : cover_inequality_rhs (theorem_7_4_cover (n := t) t) = β := by
    simp [β, C, cover_inequality_rhs_eq,
      theorem_7_4_cover_card (n := t) t (Nat.le_refl t),
      theorem_7_4_cover_card (n := t + 1) t (Nat.le_succ t)]
  have hvalidPrevPoly :
      is_valid_inequality
        (zero_one_knapsack_polytope
          (fun i : Fin t ↦ (weights i.castSucc : ℝ)) (capacity : ℝ)) α β := by
    have hbase :=
      coverInequality_validOnKnapsackPolytope
        (fun i : Fin t ↦ weights i.castSucc)
        capacity
        (theorem_7_4_cover t)
        hCprev.toIsKnapsackCover
    simpa [hαeq, hbetaEq] using hbase
  have hvalidPrevSet :
      is_valid_inequality
        (zero_one_knapsack_set
          (fun i : Fin t ↦ (weights i.castSucc : ℝ)) (capacity : ℝ)) α β := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hvalidPrevPoly
    exact is_valid_inequality_convexHull_iff.mp hvalidPrevPoly
  have hcandidateValid :
      is_valid_inequality S (Fin.snoc α (h + 1 : ℝ)) β := by
    intro x hx
    have hxData := (mem_zero_one_knapsack_set_iff _ _ _).mp hx
    rcases hxData.1 (Fin.last t) with hxlast | hxlast
    · have hy :
          (fun i : Fin t ↦ x i.castSucc) ∈
            zero_one_knapsack_set
              (fun i : Fin t ↦ (weights i.castSucc : ℝ)) (capacity : ℝ) := by
        rw [mem_zero_one_knapsack_set_iff]
        constructor
        · intro i
          exact hxData.1 i.castSucc
        · simpa [Fin.sum_univ_castSucc, hxlast] using hxData.2
      have hyValid := hvalidPrevSet hy
      have hpartialEq :
          partial_lifting_value α x = α ⬝ᵥ (fun i : Fin t ↦ x i.castSucc) := by
        simp [partial_lifting_value, dotProduct]
      -- On the zero slice the candidate reduces to the old cover inequality.
      rw [dotProduct_last_coordinate_lifting_coeffs, hxlast, mul_zero, add_zero, hpartialEq]
      exact hyValid
    · let Z : Finset (Fin (t + 1)) := C.filter fun i ↦ x i = 0
      have hZsubset : Z ⊆ C := by
        intro i hi
        exact (Finset.mem_filter.mp hi).1
      have hZcard : h + 2 ≤ Z.card := by
        by_contra hnot
        have hZcardLe : Z.card ≤ h + 1 := by omega
        have hZsubsetPrefix : Z ⊆ theorem_7_4_cover (n := t + 1) t := by
          simpa [C] using hZsubset
        have hZweight : Z.sum weights ≤ theorem_7_4_mu weights t (Nat.le_succ t) (h + 1) :=
          le_trans
            (descendingPrefixSubsetSum_le_muCard
              weights t (Nat.le_succ t) hdescending Z hZsubsetPrefix)
            (theorem_7_4_mu_mono weights t (Nat.le_succ t) hZcardLe)
        let X : Finset (Fin (t + 1)) := Finset.univ.filter fun i ↦ x i = 1
        have hXcapacity : X.sum weights ≤ capacity := by
          have hsupportWeight :
              ∑ i, (weights i : ℝ) * x i = ((X.sum weights : ℕ) : ℝ) := by
            calc
              ∑ i, (weights i : ℝ) * x i =
                  ∑ i, if i ∈ X then (weights i : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hiX : i ∈ X
                · have hxi : x i = 1 := (Finset.mem_filter.mp hiX).2
                  simp [hiX, hxi]
                · have hxi : x i = 0 := by
                    rcases hxData.1 i with hzero | hone
                    · exact hzero
                    · exact False.elim (hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hone⟩))
                  simp [hiX, hxi]
              _ = X.sum (fun i ↦ (weights i : ℝ)) := by
                simp only [X, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
              _ = ((X.sum weights : ℕ) : ℝ) := by rw [Nat.cast_sum]
          have hreal : ((X.sum weights : ℕ) : ℝ) ≤ capacity := by
            simpa [hsupportWeight] using hxData.2
          exact_mod_cast hreal
        have hjX : Fin.last t ∈ X :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxlast⟩
        have hselectedSubset : insert (Fin.last t) (C \ Z) ⊆ X := by
          intro i hi
          rcases Finset.mem_insert.mp hi with hiLast | hiCover
          · simpa [hiLast] using hjX
          · have hiC : i ∈ C := (Finset.mem_sdiff.mp hiCover).1
            have hiZ : i ∉ Z := (Finset.mem_sdiff.mp hiCover).2
            rcases hxData.1 i with hzero | hone
            · exact False.elim (hiZ (Finset.mem_filter.mpr ⟨hiC, hzero⟩))
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hone⟩
        have hselectedWeight :
            (insert (Fin.last t) (C \ Z)).sum weights ≤ X.sum weights :=
          Finset.sum_le_sum_of_subset_of_nonneg hselectedSubset
            (fun _ _ _ ↦ Nat.zero_le _)
        have hcoverSplit : Z.sum weights + (C \ Z).sum weights = C.sum weights := by
          simpa [add_comm] using Finset.sum_sdiff hZsubset (f := weights)
        have hlastNotDiff : Fin.last t ∉ C \ Z := by
          intro hi
          exact hjLast (Finset.mem_sdiff.mp hi).1
        have hselectedCapacity : weights (Fin.last t) + (C \ Z).sum weights ≤ capacity := by
          calc
            weights (Fin.last t) + (C \ Z).sum weights =
                (insert (Fin.last t) (C \ Z)).sum weights := by
              rw [Finset.sum_insert hlastNotDiff]
            _ ≤ X.sum weights := hselectedWeight
            _ ≤ capacity := hXcapacity
        have hcoverSum : C.sum weights = theorem_7_4_mu weights t (Nat.le_succ t) t := by
          simpa [C] using theorem_7_4_cover_sum_eq_mu weights t (Nat.le_succ t)
        have hcoverLarge : capacity < C.sum weights :=
          (isKnapsackCover_iff weights capacity C).mp hC.toIsKnapsackCover
        -- Too few zero cover coordinates would make a feasible point heavier than the cover.
        unfold theorem_7_4_boundary_interval_condition theorem_7_4_cover_excess at hinterval
        omega
      have hcoverBinary : ∀ i ∈ C, x i = 0 ∨ x i = 1 := by
        intro i hi
        exact hxData.1 i
      have hcoverSumX :
          C.sum x = ((C.card - Z.card : ℕ) : ℝ) := by
        simpa [Z] using theorem_7_4_sum_binary_eq_card_sub_zeros C x hcoverBinary
      have hprefixSum :
          ∑ i : Fin t, x i.castSucc = ((t - Z.card : ℕ) : ℝ) := by
        have hreindex : C.sum x = ∑ i : Fin t, x i.castSucc := by
          dsimp [C]
          rw [theorem_7_4_cover_eq_castSuccImage (Nat.le_refl t), Finset.sum_map, hprevUniv]
          rfl
        rw [← hreindex, hcoverSumX]
        simp [C, theorem_7_4_cover_card (n := t + 1) t (Nat.le_succ t)]
      have hZcardLe : Z.card ≤ t := by
        calc
          Z.card ≤ C.card := Finset.card_le_card hZsubset
          _ = t := by simp [C, theorem_7_4_cover_card (n := t + 1) t (Nat.le_succ t)]
      have hnat : t - Z.card + (h + 1) ≤ t - 1 := by omega
      have hreal :
          ((t - Z.card : ℕ) : ℝ) + ((h + 1 : ℕ) : ℝ) ≤ ((t - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have htPositive : 1 ≤ t := by omega
      have hbetaValue : β = (t : ℝ) - 1 := by
        dsimp [β, C]
        rw [cover_inequality_rhs_eq,
          theorem_7_4_cover_card (n := t + 1) t (Nat.le_succ t)]
      have hpartialValue :
          partial_lifting_value α x = ((t - Z.card : ℕ) : ℝ) := by
        simpa [partial_lifting_value, α] using hprefixSum
      rw [dotProduct_last_coordinate_lifting_coeffs, hxlast]
      rw [hpartialValue, hbetaValue]
      norm_num [Nat.cast_sub htPositive] at hreal ⊢
      exact hreal
  constructor
  · -- The preceding binary argument proves that `h + 1` is an admissible first coefficient.
    exact mem_valid_last_coordinate_lifting_coefficients_iff.mpr hcandidateValid
  · intro σ hσ
    have hσValidSet : is_valid_inequality S (Fin.snoc α σ) β :=
      mem_valid_last_coordinate_lifting_coefficients_iff.mp hσ
    have hσValidPoly :
        is_valid_inequality
          (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
          (Fin.snoc α σ) β := by
      rw [zero_one_knapsack_polytope_eq_convexHull]
      exact is_valid_inequality_convexHull_iff.mpr hσValidSet
    have hσCover : ∀ i ∈ C, (Fin.snoc α σ : Fin (t + 1) → ℝ) i = 1 := by
      intro i hi
      rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
      · simp [α]
      · exact False.elim (hjLast hi)
    have hσLifting :
        Fin.snoc α σ ∈ valid_liftings_of_minimal_cover_inequality weights capacity C :=
      mem_valid_liftings_of_minimal_cover_inequality_iff.mpr ⟨hσCover, hσValidPoly⟩
    -- The already-proved boundary upper bound applies to every valid first-stage coefficient.
    simpa [S, α, β, C] using
      theorem_7_4_boundary_interval_upper_bound
        weights capacity t (Nat.le_succ t) hweights_le hC hσLifting hjLast hh hinterval

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the boundary coefficient
`h + 1` produces a facet at the first stage containing the prefix cover and one new coordinate. -/
private theorem boundaryFirstStageFacetLifting
    (weights : Fin (t + 1) → ℕ)
    (capacity : ℕ)
    (hweights_le : ∀ i, weights i ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hdescending : theorem_7_4_cover_weights_descending weights (Nat.le_succ t))
    {h : ℕ}
    (hh : h < t)
    (hinterval :
      theorem_7_4_boundary_interval_condition
        weights capacity t (Nat.le_succ t) (Fin.last t) h) :
    Fin.snoc (fun _ : Fin t ↦ (1 : ℝ)) (h + 1 : ℝ) ∈
      facet_defining_liftings_of_minimal_cover_inequality
        weights capacity (theorem_7_4_cover t) := by
  have hCprev :
      IsMinimalKnapsackCover
        (fun i : Fin t ↦ weights i.castSucc) capacity (theorem_7_4_cover t) :=
    theorem_7_4_minimalCover_castSucc capacity (Nat.le_refl t) weights hC
  have hweightsPrev : ∀ i : Fin t, weights i.castSucc ≤ capacity := by
    intro i
    exact hweights_le i.castSucc
  have hbaseFacet :
      (fun _ : Fin t ↦ (1 : ℝ)) ∈
        facet_defining_liftings_of_minimal_cover_inequality
          (fun i : Fin t ↦ weights i.castSucc) capacity (theorem_7_4_cover t) :=
    theorem_7_4_univCoverFacetLifting
      (fun i : Fin t ↦ weights i.castSucc) capacity hweightsPrev hCprev
  have htwo : 2 ≤ t := by
    simpa [theorem_7_4_cover_card (n := t + 1) t (Nat.le_succ t)] using
      cover_card_ge_two weights capacity hweights_le _ hC.toIsKnapsackCover
  obtain ⟨γ, hγfacet, hγgreatest⟩ :=
    theorem_7_4_existsSuccessorFacetLifting
      weights capacity (Nat.le_refl t) htwo hweights_le hbaseFacet
  have hboundaryGreatest :=
    boundaryFirstStageCoefficientIsGreatest
      weights capacity hweights_le hC hdescending hh hinterval
  have hγle : γ ≤ (h + 1 : ℝ) := hboundaryGreatest.2 hγgreatest.1
  have hcandidateLe : (h + 1 : ℝ) ≤ γ := hγgreatest.2 hboundaryGreatest.1
  have hγeq : γ = (h + 1 : ℝ) := le_antisymm hγle hcandidateLe
  -- Uniqueness of the greatest valid coefficient identifies the Proposition 7.2 lift.
  simpa [hγeq] using hγfacet

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a permutation of indices
induces the corresponding continuous linear equivalence on coordinate vectors. -/
private def theorem_7_4_reindexCoordinateEquiv
    (e : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n ↦ ℝ) e.symm).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the coordinate equivalence
places the old coordinate `e i` at the reindexed coordinate `i`. -/
private theorem theorem_7_4_reindexCoordinateEquiv_apply
    (e : Equiv.Perm (Fin n))
    (x : Fin n → ℝ)
    (i : Fin n) :
    theorem_7_4_reindexCoordinateEquiv e x (e i) = x i := by
  -- This is the computation rule for the coordinate permutation equivalence.
  change
    (Equiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e.symm).symm x (e i) = x i
  simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: dot products are invariant
under simultaneous reindexing of their coefficient and coordinate vectors. -/
private theorem theorem_7_4_dotProduct_reindex
    (e : Equiv.Perm (Fin n))
    (α x : Fin n → ℝ) :
    (fun i ↦ α (e i)) ⬝ᵥ x =
      α ⬝ᵥ theorem_7_4_reindexCoordinateEquiv e x := by
  -- Reindex the finite sum and evaluate the transported coordinate at `e i`.
  rw [dotProduct, dotProduct]
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  rw [theorem_7_4_reindexCoordinateEquiv_apply]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: a coordinate permutation
transports membership in a binary knapsack set with the correspondingly reindexed weights. -/
private theorem theorem_7_4_mem_knapsackSet_reindex_iff
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (x : Fin n → ℝ) :
    x ∈ zero_one_knapsack_set (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) ↔
      theorem_7_4_reindexCoordinateEquiv e x ∈
        zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff, mem_zero_one_knapsack_set_iff]
  constructor
  · rintro ⟨hbinary, hweight⟩
    constructor
    · intro j
      have hcoordinate := hbinary (e.symm j)
      have hindex : e (e.symm j) = j := e.apply_symm_apply j
      rw [← hindex, theorem_7_4_reindexCoordinateEquiv_apply]
      exact hcoordinate
    · have hsum :=
        theorem_7_4_dotProduct_reindex e (fun i ↦ (weights i : ℝ)) x
      have hsum' :
          (∑ i, (weights (e i) : ℝ) * x i) =
            ∑ i, (weights i : ℝ) * theorem_7_4_reindexCoordinateEquiv e x i := by
        simpa only [dotProduct] using hsum
      calc
        ∑ i, (weights i : ℝ) * theorem_7_4_reindexCoordinateEquiv e x i =
            ∑ i, (weights (e i) : ℝ) * x i := hsum'.symm
        _ ≤ capacity := hweight
  · rintro ⟨hbinary, hweight⟩
    constructor
    · intro i
      simpa [theorem_7_4_reindexCoordinateEquiv_apply] using hbinary (e i)
    · have hsum :=
        theorem_7_4_dotProduct_reindex e (fun i ↦ (weights i : ℝ)) x
      have hsum' :
          (∑ i, (weights (e i) : ℝ) * x i) =
            ∑ i, (weights i : ℝ) * theorem_7_4_reindexCoordinateEquiv e x i := by
        simpa only [dotProduct] using hsum
      calc
        ∑ i, (weights (e i) : ℝ) * x i =
            ∑ i, (weights i : ℝ) * theorem_7_4_reindexCoordinateEquiv e x i := hsum'
        _ ≤ capacity := hweight

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the coordinate equivalence
maps the reindexed binary knapsack set onto the original one. -/
private theorem theorem_7_4_knapsackSet_reindex_image
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ) :
    theorem_7_4_reindexCoordinateEquiv e ''
        zero_one_knapsack_set (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) =
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  -- The pointwise membership equivalence supplies both image inclusions.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (theorem_7_4_mem_knapsackSet_reindex_iff e weights capacity x).mp hx
  · intro hy
    refine ⟨(theorem_7_4_reindexCoordinateEquiv e).symm y, ?_, ?_⟩
    · apply (theorem_7_4_mem_knapsackSet_reindex_iff e weights capacity _).mpr
      simpa using hy
    · exact (theorem_7_4_reindexCoordinateEquiv e).apply_symm_apply y

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the coordinate equivalence
maps the reindexed knapsack polytope onto the original one. -/
private theorem theorem_7_4_knapsackPolytope_reindex_image
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ) :
    theorem_7_4_reindexCoordinateEquiv e ''
        zero_one_knapsack_polytope (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) =
      zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  -- Linear equivalences commute with convex hull, and the generating sets correspond.
  rw [zero_one_knapsack_polytope_eq_convexHull,
    zero_one_knapsack_polytope_eq_convexHull]
  calc
    theorem_7_4_reindexCoordinateEquiv e ''
          convexHull ℝ
            (zero_one_knapsack_set (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ)) =
        convexHull ℝ
          (theorem_7_4_reindexCoordinateEquiv e ''
            zero_one_knapsack_set (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ)) := by
              exact
                LinearMap.image_convexHull
                  (theorem_7_4_reindexCoordinateEquiv e).toLinearMap _
    _ = convexHull ℝ
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)) := by
          rw [theorem_7_4_knapsackSet_reindex_image]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: membership in the original
and reindexed knapsack polytopes is equivalent under the coordinate equivalence. -/
private theorem theorem_7_4_mem_knapsackPolytope_reindex_iff
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (x : Fin n → ℝ) :
    x ∈ zero_one_knapsack_polytope (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) ↔
      theorem_7_4_reindexCoordinateEquiv e x ∈
        zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  constructor
  · intro hx
    have himage :
        theorem_7_4_reindexCoordinateEquiv e x ∈
          theorem_7_4_reindexCoordinateEquiv e ''
            zero_one_knapsack_polytope
              (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) :=
      ⟨x, hx, rfl⟩
    rwa [theorem_7_4_knapsackPolytope_reindex_image] at himage
  · intro hx
    have himage :
        theorem_7_4_reindexCoordinateEquiv e x ∈
          theorem_7_4_reindexCoordinateEquiv e ''
            zero_one_knapsack_polytope
              (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) := by
      rwa [theorem_7_4_knapsackPolytope_reindex_image]
    rcases himage with ⟨y, hy, hyx⟩
    have hy_eq_x : y = x := (theorem_7_4_reindexCoordinateEquiv e).injective hyx
    simpa [hy_eq_x] using hy

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: lifted-cover coefficients
commute with a coordinate permutation that preserves the cover. -/
private theorem theorem_7_4_liftedCoverCoeff_reindex
    (e : Equiv.Perm (Fin n))
    (C : Finset (Fin n))
    (hC : ∀ i, e i ∈ C ↔ i ∈ C)
    (α : Fin n → ℝ) :
    lifted_cover_inequality_coeff C (fun i ↦ α (e i)) =
      fun i ↦ lifted_cover_inequality_coeff C α (e i) := by
  ext i
  rw [lifted_cover_inequality_coeff_apply, lifted_cover_inequality_coeff_apply]
  simp only [hC]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the reindexed lifted-cover
functional agrees with the original functional after the coordinate equivalence. -/
private theorem theorem_7_4_liftedCoverDot_reindex
    (e : Equiv.Perm (Fin n))
    (C : Finset (Fin n))
    (hC : ∀ i, e i ∈ C ↔ i ∈ C)
    (α x : Fin n → ℝ) :
    lifted_cover_inequality_coeff C (fun i ↦ α (e i)) ⬝ᵥ x =
      lifted_cover_inequality_coeff C α ⬝ᵥ
        theorem_7_4_reindexCoordinateEquiv e x := by
  calc
    lifted_cover_inequality_coeff C (fun i ↦ α (e i)) ⬝ᵥ x =
        (fun i ↦ lifted_cover_inequality_coeff C α (e i)) ⬝ᵥ x := by
          rw [theorem_7_4_liftedCoverCoeff_reindex e C hC α]
    _ = lifted_cover_inequality_coeff C α ⬝ᵥ
        theorem_7_4_reindexCoordinateEquiv e x :=
      theorem_7_4_dotProduct_reindex e _ _

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the coordinate equivalence
preserves membership in lifted-cover faces when the permutation preserves the cover. -/
private theorem theorem_7_4_mem_liftedCoverFace_reindex_iff
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (hC : ∀ i, e i ∈ C ↔ i ∈ C)
    (α x : Fin n → ℝ) :
    x ∈ lifted_cover_face
        (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) C (fun i ↦ α (e i)) ↔
      theorem_7_4_reindexCoordinateEquiv e x ∈
        lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) C α := by
  rw [lifted_cover_face, lifted_cover_face, mem_face_set_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨(theorem_7_4_mem_knapsackPolytope_reindex_iff e weights capacity x).mp hx, ?_⟩
    rw [← theorem_7_4_liftedCoverDot_reindex e C hC]
    exact heq
  · rintro ⟨hx, heq⟩
    refine ⟨(theorem_7_4_mem_knapsackPolytope_reindex_iff e weights capacity x).mpr hx, ?_⟩
    rw [theorem_7_4_liftedCoverDot_reindex e C hC]
    exact heq

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: the coordinate equivalence
maps the reindexed lifted-cover face onto the original lifted-cover face. -/
private theorem theorem_7_4_liftedCoverFace_reindex_image
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (hC : ∀ i, e i ∈ C ↔ i ∈ C)
    (α : Fin n → ℝ) :
    theorem_7_4_reindexCoordinateEquiv e ''
        lifted_cover_face
          (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) C (fun i ↦ α (e i)) =
      lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) C α := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (theorem_7_4_mem_liftedCoverFace_reindex_iff e weights capacity C hC α x).mp hx
  · intro hy
    refine ⟨(theorem_7_4_reindexCoordinateEquiv e).symm y, ?_, ?_⟩
    · apply
        (theorem_7_4_mem_liftedCoverFace_reindex_iff
          e weights capacity C hC α _).mpr
      simpa using hy
    · exact (theorem_7_4_reindexCoordinateEquiv e).apply_symm_apply y

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_theorem_7_4.lean`: facet-defining minimal-cover
liftings are invariant under a coordinate permutation that preserves the cover. -/
private theorem theorem_7_4_facetDefiningLifting_reindex_iff
    (e : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (hC : ∀ i, e i ∈ C ↔ i ∈ C)
    (α : Fin n → ℝ) :
    α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C ↔
      (fun i ↦ α (e i)) ∈
        facet_defining_liftings_of_minimal_cover_inequality
          (fun i ↦ weights (e i)) capacity C := by
  rw [mem_facet_defining_liftings_of_minimal_cover_inequality_iff,
    mem_facet_defining_liftings_of_minimal_cover_inequality_iff]
  have hfacetTransport :
      α ∈ facet_defining_liftings_of_cover_inequality
          (fun i ↦ (weights i : ℝ)) (capacity : ℝ) C ↔
        (fun i ↦ α (e i)) ∈ facet_defining_liftings_of_cover_inequality
          (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) C := by
    rw [mem_facet_defining_liftings_of_cover_inequality_iff,
      mem_facet_defining_liftings_of_cover_inequality_iff]
    have htransport :=
      isFacetOf_image_continuousLinearEquiv
        (theorem_7_4_reindexCoordinateEquiv e)
        (A := zero_one_knapsack_polytope
          (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ))
        (B := lifted_cover_face
          (fun i ↦ (weights (e i) : ℝ)) (capacity : ℝ) C (fun i ↦ α (e i)))
    rw [theorem_7_4_knapsackPolytope_reindex_image,
      theorem_7_4_liftedCoverFace_reindex_image e weights capacity C hC α] at htransport
    exact htransport.symm
  constructor
  · rintro ⟨hvalid, hfacet⟩
    constructor
    · rw [mem_valid_liftings_of_minimal_cover_inequality_iff] at hvalid ⊢
      constructor
      · intro i hi
        exact hvalid.1 (e i) ((hC i).mpr hi)
      · rw [is_valid_inequality_iff] at hvalid ⊢
        intro x hx
        have hineq :=
          hvalid.2 ((theorem_7_4_mem_knapsackPolytope_reindex_iff e weights capacity x).mp hx)
        rw [theorem_7_4_dotProduct_reindex]
        exact hineq
    · exact hfacetTransport.mp hfacet
  · rintro ⟨hvalid, hfacet⟩
    constructor
    · rw [mem_valid_liftings_of_minimal_cover_inequality_iff] at hvalid ⊢
      constructor
      · intro j hj
        have himage : e (e.symm j) ∈ C := by simpa using hj
        have hprefix := (hC (e.symm j)).mp himage
        have hcoeff := hvalid.1 (e.symm j) hprefix
        simpa using hcoeff
      · rw [is_valid_inequality_iff] at hvalid ⊢
        intro y hy
        have hyimage :
            theorem_7_4_reindexCoordinateEquiv e
                ((theorem_7_4_reindexCoordinateEquiv e).symm y) ∈
              zero_one_knapsack_polytope
                (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
          simpa using hy
        have hpreimage :=
          (theorem_7_4_mem_knapsackPolytope_reindex_iff
            e weights capacity ((theorem_7_4_reindexCoordinateEquiv e).symm y)).mpr hyimage
        have hineq := hvalid.2 hpreimage
        rw [theorem_7_4_dotProduct_reindex] at hineq
        simpa using hineq
    · exact hfacetTransport.mpr hfacet

/-- Theorem 7.4 (3). Under the same hypotheses as Theorem 7.4, if
`μ_{h+1} - λ < a_j < μ_{h+1}` for some `j ∉ C` and `h < t`, then there exists a facet-defining
lifting of the form `(7.5)` whose coefficient on `x_j` is `h + 1`. -/
theorem theorem_7_4_boundary_interval_realizes_upper_lifting_coefficient
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hC : IsMinimalKnapsackCover weights capacity (theorem_7_4_cover t))
    (hordered : theorem_7_4_cover_weights_descending weights ht)
    {j : Fin n}
    (hj : j ∉ theorem_7_4_cover t)
    {h : ℕ}
    (hh : h < t)
    (hinterval : theorem_7_4_boundary_interval_condition weights capacity t ht j h) :
    ∃ α' : Fin n → ℝ,
      α' ∈ theorem_7_4_facet_defining_liftings weights capacity t ∧
        α' j = h + 1 :=
  by
  -- The interval bounds determine the unique lifting coefficient at the off-cover index.
  classical
  have hjge : t ≤ j := by
    apply Nat.le_of_not_gt
    intro hjlt
    exact hj (theorem_7_4_cover_mem_iff.mpr hjlt)
  have htlt : t < n := lt_of_le_of_lt hjge j.isLt
  have hstageFull : t + 1 ≤ n := Nat.succ_le_of_lt htlt
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hstageFull
  have hkLt : t < t + 1 + r := by omega
  let k : Fin (t + 1 + r) := ⟨t, hkLt⟩
  let e : Equiv.Perm (Fin (t + 1 + r)) := Equiv.swap k j
  let reindexedWeights : Fin (t + 1 + r) → ℕ := fun i ↦ weights (e i)
  have heFixBelow (i : Fin (t + 1 + r)) (hi : i < t) : e i = i := by
    have hik : i ≠ k := by
      intro hik
      have hval := congrArg Fin.val hik
      dsimp [k] at hval
      omega
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hj (theorem_7_4_cover_mem_iff.mpr hi)
    simp [e, Equiv.swap_apply_of_ne_of_ne hik hij]
  have hePreservesCover :
      ∀ i : Fin (t + 1 + r),
        e i ∈ theorem_7_4_cover t ↔ i ∈ theorem_7_4_cover t := by
    intro i
    by_cases hik : i = k
    · subst i
      simp [e, k, theorem_7_4_cover_mem_iff, hj]
    · by_cases hij : i = j
      · subst i
        simp [e, k, theorem_7_4_cover_mem_iff, hj]
      · have hei : e i = i := by
          simp [e, Equiv.swap_apply_of_ne_of_ne hik hij]
        rw [hei]
  have hreindexedCover :
      IsMinimalKnapsackCover
        reindexedWeights capacity (theorem_7_4_cover t) := by
    have hsumEq
        (D : Finset (Fin (t + 1 + r)))
        (hD : D ⊆ theorem_7_4_cover t) :
        D.sum reindexedWeights = D.sum weights := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiCover := hD hi
      have hiLt : i < t := theorem_7_4_cover_mem_iff.mp hiCover
      dsimp [reindexedWeights]
      rw [heFixBelow i hiLt]
    rw [isMinimalKnapsackCover_iff] at hC ⊢
    constructor
    · rw [isKnapsackCover_iff] at hC ⊢
      rw [hsumEq (theorem_7_4_cover t) (fun _ hi ↦ hi)]
      exact hC.1
    · intro i hi
      rw [hsumEq ((theorem_7_4_cover t).erase i) (Finset.erase_subset i _)]
      exact hC.2 i hi
  have hfull : t + 1 ≤ t + 1 + r := Nat.le_add_right (t + 1) r
  let firstWeights : Fin (t + 1) → ℕ :=
    fun i ↦ reindexedWeights (i.castLE hfull)
  have hfirstWeights_le : ∀ i, firstWeights i ≤ capacity := by
    intro i
    exact hweights_le (e (i.castLE hfull))
  have hfirstCover :
      IsMinimalKnapsackCover
        firstWeights capacity (theorem_7_4_cover t) := by
    simpa [firstWeights] using
      theorem_7_4_minimalCover_castLE
        (t + 1) r t (Nat.le_succ t) reindexedWeights capacity hreindexedCover
  have hfirstCoverWeight
      (i : Fin t) :
      theorem_7_4_cover_weight firstWeights (Nat.le_succ t) i =
        theorem_7_4_cover_weight weights ht i := by
    have hiLt :
        (i.castLE (Nat.le_succ t)).castLE hfull < t := by
      exact i.isLt
    dsimp [theorem_7_4_cover_weight, firstWeights, reindexedWeights]
    rw [heFixBelow _ hiLt]
    apply congrArg weights
    exact Fin.ext rfl
  have hfirstDescending :
      theorem_7_4_cover_weights_descending firstWeights (Nat.le_succ t) := by
    rw [theorem_7_4_cover_weights_descending_iff] at hordered ⊢
    intro i l hil
    rw [hfirstCoverWeight, hfirstCoverWeight]
    exact hordered hil
  have hmuEq (q : ℕ) :
      theorem_7_4_mu firstWeights t (Nat.le_succ t) q =
        theorem_7_4_mu weights t ht q := by
    unfold theorem_7_4_mu
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlt : l < t
    · simp only [hlt, ↓reduceDIte]
      dsimp [firstWeights, reindexedWeights]
      have hindexLt :
          (⟨l, Nat.lt_of_lt_of_le hlt ht⟩ : Fin (t + 1 + r)) < t := by
        simpa
      rw [heFixBelow _ hindexLt]
    · simp [hlt]
  have hcoverExcessEq :
      theorem_7_4_cover_excess firstWeights capacity t (Nat.le_succ t) =
        theorem_7_4_cover_excess weights capacity t ht := by
    unfold theorem_7_4_cover_excess
    rw [hmuEq]
  have hlastIndex : (Fin.last t).castLE hfull = k := by
    exact Fin.ext rfl
  have hlastWeight : firstWeights (Fin.last t) = weights j := by
    dsimp [firstWeights, reindexedWeights]
    rw [hlastIndex]
    simp [e]
  have hfirstInterval :
      theorem_7_4_boundary_interval_condition
        firstWeights capacity t (Nat.le_succ t) (Fin.last t) h := by
    unfold theorem_7_4_boundary_interval_condition at hinterval ⊢
    rw [hmuEq, hcoverExcessEq, hlastWeight]
    exact hinterval
  have hfirstFacet :
      Fin.snoc (fun _ : Fin t ↦ (1 : ℝ)) (h + 1 : ℝ) ∈
        facet_defining_liftings_of_minimal_cover_inequality
          firstWeights capacity (theorem_7_4_cover t) :=
    boundaryFirstStageFacetLifting
      firstWeights capacity hfirstWeights_le hfirstCover hfirstDescending hh hfirstInterval
  have htwo : 2 ≤ t := by
    simpa [theorem_7_4_cover_card (n := t + 1 + r) t
      (Nat.le_trans (Nat.le_succ t) hfull)] using
      cover_card_ge_two weights capacity hweights_le _ hC.1
  obtain ⟨αReindexed, hαReindexed, hpreserved⟩ :=
    theorem_7_4_existsFacetLiftingExtension
      (t + 1) r t (Nat.le_succ t) htwo reindexedWeights capacity
      (fun i ↦ hweights_le (e i))
      (Fin.snoc (fun _ : Fin t ↦ (1 : ℝ)) (h + 1 : ℝ)) hfirstFacet
  let α' : Fin (t + 1 + r) → ℝ := fun i ↦ αReindexed (e.symm i)
  have hα' :
      α' ∈ theorem_7_4_facet_defining_liftings weights capacity t := by
    apply
      (theorem_7_4_facetDefiningLifting_reindex_iff
        e weights capacity (theorem_7_4_cover t) hePreservesCover α').mpr
    simpa [α'] using hαReindexed
  have hpreservedLast := hpreserved (Fin.last t)
  have hαReindexedK : αReindexed k = h + 1 := by
    rw [← hlastIndex]
    simpa using hpreservedLast
  have hα'j : α' j = h + 1 := by
    dsimp [α']
    simpa [e] using hαReindexedK
  -- Transport the completed facet back through the same swap; the chosen coefficient is fixed.
  exact ⟨α', hα', hα'j⟩

end Theorem74

#print axioms theorem_7_4_forces_exact_lifting_coefficient
#print axioms theorem_7_4_bounds_lifting_coefficient_on_boundary_interval
#print axioms theorem_7_4_boundary_interval_realizes_upper_lifting_coefficient
