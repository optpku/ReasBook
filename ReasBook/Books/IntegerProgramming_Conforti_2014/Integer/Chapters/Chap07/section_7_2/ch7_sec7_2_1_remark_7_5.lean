/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_knapsack_cover
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_proposition_7_2

open scoped BigOperators Matrix

section Remark75

variable {n : ℕ}

/-- The prefix cover `{1, ..., t}` from the Theorem 7.4 setup, represented on `Fin n` by the
indices `< t`. -/
def remark_7_5_cover
    (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i < t

/-- Membership in `remark_7_5_cover t` means that the index lies among the first `t`
positions. -/
@[simp] theorem remark_7_5_cover_mem_iff
    {t : ℕ}
    {j : Fin n} :
    j ∈ remark_7_5_cover t ↔ j < t := by
  simp [remark_7_5_cover]

/-- The ordered cover weights `a₁, ..., a_t` from the Theorem 7.4 setup, reindexed as a function
on `Fin t`. -/
def remark_7_5_cover_weight
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Fin t → ℕ :=
  fun i ↦ weights (i.castLE ht)

/-- `remark_7_5_cover_weights_descending weights ht` records the ordering
`a₁ ≥ a₂ ≥ ··· ≥ a_t` from the Theorem 7.4 hypotheses. -/
def remark_7_5_cover_weights_descending
    (weights : Fin n → ℕ)
    {t : ℕ}
    (ht : t ≤ n) : Prop :=
  Antitone (remark_7_5_cover_weight weights ht)

/-- The partial sums `μ_h = ∑_{ℓ=1}^h a_ℓ` from the Theorem 7.4 setup, extended to all natural
indices by summing the first `h` ordered cover weights among the first `t` positions. -/
def remark_7_5_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) : ℕ → ℕ :=
  fun h ↦
    (Finset.range h).sum fun ℓ ↦
      if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0

/-- Helper for Remark 7.5: the prefix cover `{i | i < t}` is exactly the image of `Fin t` in
`Fin n` under `Fin.castLE ht`. -/
theorem remark_7_5_cover_eq_castLEImage
    (t : ℕ)
    (ht : t ≤ n) :
    remark_7_5_cover (n := n) t =
      (Finset.univ : Finset (Fin t)).map
        ⟨fun i ↦ i.castLE ht, by
          intro a b hab
          exact Fin.ext (congrArg (fun x : Fin n ↦ x.1) hab)
        ⟩ := by
  ext j
  constructor
  · intro hj
    rw [Finset.mem_map]
    refine ⟨⟨j, remark_7_5_cover_mem_iff.mp hj⟩, by simp, ?_⟩
    simp
  · intro hj
    rw [Finset.mem_map] at hj
    rcases hj with ⟨i, -, hij⟩
    subst hij
    simp [remark_7_5_cover]

/-- Helper for Remark 7.5: summing the weights over the prefix cover gives the partial sum
`μ_t`. -/
theorem remark_7_5_cover_sum_eq_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n) :
    (remark_7_5_cover t).sum weights = remark_7_5_mu weights t ht t := by
  let g : ℕ → ℕ := fun ℓ ↦
    if hℓ : ℓ < t then weights ⟨ℓ, Nat.lt_of_lt_of_le hℓ ht⟩ else 0
  -- Reindex the prefix cover by the canonical embedding `Fin t ↪ Fin n`.
  rw [remark_7_5_cover_eq_castLEImage (n := n) t ht]
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
    _ = remark_7_5_mu weights t ht t := by
          simp [g, remark_7_5_mu]

/-- Helper for Remark 7.5: evaluating `μ_s` inside a larger Theorem 7.4 context agrees with
evaluating the same prefix sum in the shorter prefix problem. -/
theorem remark_7_5_mu_prefix_eq
    (weights : Fin n → ℕ)
    {s t : ℕ}
    (hsn : s ≤ n)
    (htn : t ≤ n)
    (hst : s ≤ t) :
    remark_7_5_mu weights s hsn s = remark_7_5_mu weights t htn s := by
  -- Every summand in `range s` lies below both cutoffs `s` and `t`.
  unfold remark_7_5_mu
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hℓs : ℓ < s := Finset.mem_range.mp hℓ
  have hℓt : ℓ < t := Nat.lt_of_lt_of_le hℓs hst
  simp [hℓs, hℓt]

/-- Helper for Remark 7.5: once the partial-sum index has reached the cover length `t`, adding one
more index does not change `μ`. -/
theorem remark_7_5_mu_succ_of_ge
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hs : t ≤ s) :
    remark_7_5_mu weights t ht (s + 1) = remark_7_5_mu weights t ht s := by
  -- Past the first `t` cover positions, the extra summand is the forced zero branch.
  rw [remark_7_5_mu, remark_7_5_mu, Finset.sum_range_succ]
  simp [Nat.not_lt.mpr hs]

/-- Helper for Remark 7.5: the partial sums stabilize at `μ_t` for every index `s ≥ t`. -/
theorem remark_7_5_mu_eq_of_ge
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hs : t ≤ s) :
    remark_7_5_mu weights t ht s = remark_7_5_mu weights t ht t := by
  -- Step from `t` to `s` using the fact that every later increment is zero.
  rcases Nat.exists_eq_add_of_le hs with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp
  | succ k hk =>
      have hstep :
          remark_7_5_mu weights t ht ((t + k) + 1) =
            remark_7_5_mu weights t ht (t + k) := by
        rw [remark_7_5_mu_succ_of_ge weights t ht (t + k) (Nat.le_add_right t k)]
      simpa [Nat.add_assoc] using hstep.trans (hk (Nat.le_add_right t k))

/-- The cover excess `λ = μ_t - b` coming from the Theorem 7.4 setup. -/
def remark_7_5_cover_excess
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n) : ℕ :=
  remark_7_5_mu weights t ht t - capacity

/-- `remark_7_5_theorem_7_4_context weights capacity C μ λ` packages the source-faithful
background from Theorem 7.4 that Remark 7.5 refers back to: `C` is the distinguished prefix
minimal cover, the cover weights are ordered, every item weight lies in `(0, capacity]`, `μ` is
the associated partial-sum sequence, and `λ` is the cover excess. -/
def remark_7_5_theorem_7_4_context
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (lam : ℕ) : Prop :=
  ∃ t, ∃ ht : t ≤ n,
    C = remark_7_5_cover t ∧
      remark_7_5_cover_weights_descending weights ht ∧
      (∀ j, 0 < weights j) ∧
      (∀ j, weights j ≤ capacity) ∧
      IsMinimalKnapsackCover weights capacity C ∧
      μ = remark_7_5_mu weights t ht ∧
      lam = remark_7_5_cover_excess weights capacity t ht

/-- The coefficient vector from Remark 7.5: it has value `1` on the cover `C` and value `h(j)` on
the complement `N \ C`. -/
abbrev remark_7_5_lifting_coeff
    (C : Finset (Fin n))
    (h : Fin n → ℕ) : Fin n → ℝ :=
  lifted_cover_inequality_coeff C fun j ↦ (h j : ℝ)

/-- Evaluating `remark_7_5_lifting_coeff C h` at `j` recovers the piecewise coefficient formula
from Remark 7.5. -/
theorem remark_7_5_lifting_coeff_apply
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    (j : Fin n) :
    remark_7_5_lifting_coeff C h j = if j ∈ C then 1 else (h j : ℝ) := by
  exact lifted_cover_inequality_coeff_apply C (fun k ↦ (h k : ℝ)) j

/-- On the cover `C`, the coefficient vector from Remark 7.5 has coefficient `1`. -/
@[simp] theorem remark_7_5_lifting_coeff_apply_of_mem
    {C : Finset (Fin n)}
    {h : Fin n → ℕ}
    {j : Fin n}
    (hj : j ∈ C) :
    remark_7_5_lifting_coeff C h j = 1 := by
  simp [remark_7_5_lifting_coeff, hj]

/-- Off the cover `C`, the coefficient vector from Remark 7.5 has coefficient `h(j)`. -/
@[simp] theorem remark_7_5_lifting_coeff_apply_of_not_mem
    {C : Finset (Fin n)}
    {h : Fin n → ℕ}
    {j : Fin n}
    (hj : j ∉ C) :
    remark_7_5_lifting_coeff C h j = (h j : ℝ) := by
  simp [remark_7_5_lifting_coeff, hj]

/-- Dotting the coefficient vector from Remark 7.5 with `x` gives the source formula
`∑_{j ∈ C} x_j + ∑_{j ∈ N \ C} h(j) x_j`. -/
theorem remark_7_5_lifting_coeff_dotProduct
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    (x : Fin n → ℝ) :
    remark_7_5_lifting_coeff C h ⬝ᵥ x =
      Finset.sum C (fun j ↦ x j) +
        Finset.sum (Finset.univ \ C) (fun j ↦ (h j : ℝ) * x j) := by
  -- This is exactly the generic lifted-cover dot-product identity specialized to `α j = h j`.
  simpa [remark_7_5_lifting_coeff] using
    lifted_cover_inequality_coeff_dotProduct C (fun j ↦ (h j : ℝ)) x

/-- `remark_7_5_interval_indices weights C μ h` records the interval condition
`μ_{h(j)} ≤ a_j < μ_{h(j)+1}` for every index `j` outside the cover `C`. -/
def remark_7_5_interval_indices
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ) : Prop :=
  ∀ j, j ∉ C → μ (h j) ≤ weights j ∧ weights j < μ (h j + 1)

/-- Expanding `remark_7_5_interval_indices weights C μ h` recovers the interval-index condition
from Remark 7.5. -/
theorem remark_7_5_interval_indices_iff
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ) :
    remark_7_5_interval_indices weights C μ h ↔
      ∀ j, j ∉ C → μ (h j) ≤ weights j ∧ weights j < μ (h j + 1) :=
  Iff.rfl

/-- `remark_7_5_strong_upper_bound weights C μ h λ` records the strengthened hypothesis
`a_j ≤ μ_{h(j)+1} - λ` for every `j ∈ N \ C`. -/
def remark_7_5_strong_upper_bound
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ) : Prop :=
  ∀ j, j ∉ C → weights j ≤ μ (h j + 1) - lam

/-- Expanding `remark_7_5_strong_upper_bound weights C μ h λ` recovers the strengthened upper
bound hypothesis from Remark 7.5. -/
theorem remark_7_5_strong_upper_bound_iff
    (weights : Fin n → ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ) :
    remark_7_5_strong_upper_bound weights C μ h lam ↔
      ∀ j, j ∉ C → weights j ≤ μ (h j + 1) - lam :=
  Iff.rfl

/-- Helper for Remark 7.5: a shorter prefix cover is contained in a longer one. -/
theorem remark_7_5_cover_subset
    {s t : ℕ}
    (hst : s ≤ t) :
    remark_7_5_cover (n := n) s ⊆ remark_7_5_cover t := by
  -- Membership is just the corresponding strict inequality on indices.
  intro i hi
  exact remark_7_5_cover_mem_iff.mpr
    (Nat.lt_of_lt_of_le (remark_7_5_cover_mem_iff.mp hi) hst)

/-- Helper for Remark 7.5: the prefix cover `{i | i < t}` has exactly `t` elements when
`t ≤ n`. -/
theorem remark_7_5_cover_card
    (t : ℕ)
    (ht : t ≤ n) :
    (remark_7_5_cover (n := n) t).card = t := by
  -- Reindex the prefix cover by `Fin t`.
  rw [remark_7_5_cover_eq_castLEImage (n := n) t ht]
  simp

/-- Helper for Remark 7.5: filtering the prefix cover by `s ≤ i` removes the shorter prefix
`remark_7_5_cover s`. -/
theorem remark_7_5_cover_filter_ge_eq_sdiff
    (t s : ℕ) :
    (remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) =
      remark_7_5_cover t \ remark_7_5_cover s := by
  -- On the prefix cover, `s ≤ i` is equivalent to `i ∉ remark_7_5_cover s`.
  ext i
  simp [remark_7_5_cover_mem_iff]

/-- Helper for Remark 7.5: the weights on the suffix `{i ∈ C | s ≤ i}` sum to `μ_t - μ_s`. -/
theorem remark_7_5_cover_suffix_sum_eq
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (s : ℕ)
    (hst : s ≤ t) :
    ((remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).sum weights =
      remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s := by
  -- Rewrite the suffix as a set difference and compare the two prefix sums.
  rw [remark_7_5_cover_filter_ge_eq_sdiff]
  have hsubset : remark_7_5_cover (n := n) s ⊆ remark_7_5_cover t :=
    remark_7_5_cover_subset (n := n) hst
  have hsdiff :
      (remark_7_5_cover t \ remark_7_5_cover s).sum weights +
          (remark_7_5_cover s).sum weights =
        (remark_7_5_cover t).sum weights := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_sdiff hsubset (f := weights))
  have hs_sum :
      (remark_7_5_cover s).sum weights = remark_7_5_mu weights t ht s := by
    calc
      (remark_7_5_cover s).sum weights = remark_7_5_mu weights s (Nat.le_trans hst ht) s := by
        rw [remark_7_5_cover_sum_eq_mu]
      _ = remark_7_5_mu weights t ht s := by
        rw [remark_7_5_mu_prefix_eq weights (Nat.le_trans hst ht) ht hst]
  have hsdiff' :
      (remark_7_5_cover t \ remark_7_5_cover s).sum weights +
          remark_7_5_mu weights t ht s =
        remark_7_5_mu weights t ht t := by
    calc
      (remark_7_5_cover t \ remark_7_5_cover s).sum weights + remark_7_5_mu weights t ht s
          = (remark_7_5_cover t \ remark_7_5_cover s).sum weights +
              (remark_7_5_cover s).sum weights := by rw [← hs_sum]
      _ = (remark_7_5_cover t).sum weights := hsdiff
      _ = remark_7_5_mu weights t ht t := by rw [remark_7_5_cover_sum_eq_mu]
  exact Nat.eq_sub_of_add_eq hsdiff'

/-- Helper for Remark 7.5: the suffix `{i ∈ C | s ≤ i}` has exactly `t - s` elements. -/
theorem remark_7_5_cover_suffix_card
    (t s : ℕ)
    (ht : t ≤ n)
    (hst : s ≤ t) :
    ((remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))).card = t - s := by
  -- Rewrite the suffix as a difference of the two prefix covers and compare cardinalities.
  rw [remark_7_5_cover_filter_ge_eq_sdiff]
  rw [Finset.card_sdiff_of_subset (remark_7_5_cover_subset (n := n) hst)]
  rw [remark_7_5_cover_card (n := n) t ht, remark_7_5_cover_card (n := n) s (Nat.le_trans hst ht)]

/-- Helper for Remark 7.5: the explicit suffix witness is supported on the off-cover index `j`
and the cover suffix `{i ∈ C | s ≤ i}`. -/
private def remark_7_5_suffixWitnessSupport
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Finset (Fin n) :=
  insert j ((remark_7_5_cover t).filter fun i : Fin n ↦ s ≤ (i : ℕ))

/-- Helper for Remark 7.5: the canonical suffix witness is the binary indicator of the support
`{j} ∪ {i ∈ C | s ≤ i}` used in the interval and upper-bound arguments. -/
private def remark_7_5_suffixWitness
    (t : ℕ)
    (j : Fin n)
    (s : ℕ) : Fin n → ℝ :=
  fun i ↦ if i ∈ remark_7_5_suffixWitnessSupport t j s then 1 else 0

/-- Helper for Remark 7.5: an off-cover index never belongs to the chosen cover suffix. -/
private theorem remark_7_5_not_mem_cover_suffix
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ) :
    j ∉ (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) := by
  -- The suffix stays inside the cover, so an off-cover pivot cannot lie in it.
  intro hjSuffix
  exact hj ((Finset.mem_filter.mp hjSuffix).1)

/-- Helper for Remark 7.5: the suffix witness splits as the cover-suffix indicator plus the
singleton vector at the off-cover pivot. -/
private theorem remark_7_5_suffixWitness_eq
    {t : ℕ}
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ) :
    remark_7_5_suffixWitness t j s =
      cover_indicator ((remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))) +
        Pi.single j (1 : ℝ) := by
  funext i
  by_cases hij : i = j
  · subst i
    -- On the pivot coordinate, only the singleton term survives.
    have hjsuffix :
        j ∉ (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ)) :=
      remark_7_5_not_mem_cover_suffix (j := j) hj s
    simp [remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport, cover_indicator, hjsuffix]
  · by_cases hi :
      i ∈ (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
    · -- On the suffix, both descriptions are the same indicator value.
      simp [remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport, cover_indicator, hi, hij]
    · -- Away from the suffix and the pivot, both sides vanish.
      simp [remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport, cover_indicator, hi, hij]

/-- Helper for Remark 7.5: the suffix witness weight equals the pivot weight plus the chosen
cover-suffix weight `μ_t - μ_s`. -/
private theorem remark_7_5_suffixWitnessWeight
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    ∑ i, (weights i : ℝ) * remark_7_5_suffixWitness t j s i =
      (weights j : ℝ) +
        (((remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s : ℕ) : ℝ)) := by
  let suffix :=
    (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum :
      suffix.sum weights =
        remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s := by
    simpa [suffix] using remark_7_5_cover_suffix_sum_eq weights t ht s hst
  -- Rewrite the witness through the suffix indicator plus the singleton pivot.
  calc
    ∑ i, (weights i : ℝ) * remark_7_5_suffixWitness t j s i
      = (fun i ↦ (weights i : ℝ)) ⬝ᵥ remark_7_5_suffixWitness t j s := by
          simp [dotProduct]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [remark_7_5_suffixWitness_eq (j := j) hj s]
    _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ cover_indicator suffix +
          (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
          rw [dotProduct_add]
    _ = suffix.sum (fun i ↦ (weights i : ℝ)) + weights j := by
          rw [dotProduct_comm, coverIndicator_dot_eq_sum]
          simp
    _ = (((suffix.sum weights : ℕ) : ℝ)) + weights j := by
          rw [Nat.cast_sum]
    _ = (weights j : ℝ) +
          (((remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s : ℕ) : ℝ)) := by
          rw [hsuffix_sum]
          ring

/-- Helper for Remark 7.5: any coefficient vector that is `1` on the cover evaluates on the
suffix witness as the pivot coefficient plus the suffix cardinality `t - s`. -/
private theorem remark_7_5_suffixWitnessCoeff
    (t : ℕ)
    (ht : t ≤ n)
    {α : Fin n → ℝ}
    (hαcover : ∀ i ∈ remark_7_5_cover t, α i = 1)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ)
    (hst : s ≤ t) :
    α ⬝ᵥ remark_7_5_suffixWitness t j s = α j + (t - s : ℝ) := by
  let suffix :=
    (remark_7_5_cover t).filter (fun i : Fin n ↦ s ≤ (i : ℕ))
  have hsuffix_sum_one :
      suffix.sum α = suffix.sum (fun _ ↦ (1 : ℝ)) := by
    -- On the suffix, the lifting agrees with the base cover coefficient.
    apply Finset.sum_congr rfl
    intro i hi
    exact hαcover i ((Finset.mem_filter.mp hi).1)
  calc
    α ⬝ᵥ remark_7_5_suffixWitness t j s
      = α ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
          rw [remark_7_5_suffixWitness_eq (j := j) hj s]
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
          rw [remark_7_5_cover_suffix_card (n := n) t s ht hst, Nat.cast_sub hst]
          ring

/-- Helper for Remark 7.5: once the normalized residual-weight inequality is known, the suffix
witness is a feasible binary knapsack point. -/
private theorem remark_7_5_suffixWitnessFeasible
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover t)
    (s : ℕ)
    (hst : s ≤ t)
    (hfeasible :
      (weights j : ℝ) +
        (((remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht s : ℕ) : ℝ)) ≤ capacity) :
    remark_7_5_suffixWitness t j s ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · -- The witness is an indicator, so every coordinate is binary.
    intro i
    by_cases hi : i ∈ remark_7_5_suffixWitnessSupport t j s
    · right
      simp [remark_7_5_suffixWitness, hi]
    · left
      simp [remark_7_5_suffixWitness, hi]
  · -- The normalized weight formula reduces feasibility to the supplied residual bound.
    rw [remark_7_5_suffixWitnessWeight (weights := weights) (t := t) (ht := ht) (j := j) hj s hst]
    exact hfeasible

/-- The valid liftings of the minimal cover inequality attached to `C` are the coefficient vectors
that keep coefficient `1` on `C` and yield a valid inequality for the `0,1` knapsack polytope. -/
def valid_liftings_of_minimal_cover_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {α |
    (∀ j ∈ C, α j = 1) ∧
      is_valid_inequality
        (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs C)}

/-- Membership in `valid_liftings_of_minimal_cover_inequality weights capacity C` means keeping
the cover coefficients equal to `1` and being valid for the knapsack polytope. -/
theorem mem_valid_liftings_of_minimal_cover_inequality_iff
    {weights : Fin n → ℕ}
    {capacity : ℕ}
    {C : Finset (Fin n)}
    {α : Fin n → ℝ} :
    α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C ↔
      (∀ j ∈ C, α j = 1) ∧
        is_valid_inequality
          (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
          α
          (cover_inequality_rhs C) :=
  Iff.rfl

/-- The facet-defining liftings of the minimal cover inequality attached to `C` are the valid
liftings whose coefficient vector also belongs to the canonical cover-lifting facet owner. -/
def facet_defining_liftings_of_minimal_cover_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {α |
    α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C ∧
      α ∈ facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        C}

/-- Membership in `facet_defining_liftings_of_minimal_cover_inequality weights capacity C` means
being a valid lifting and belonging to the canonical facet-defining cover-lifting owner. -/
theorem mem_facet_defining_liftings_of_minimal_cover_inequality_iff
    {weights : Fin n → ℕ}
    {capacity : ℕ}
    {C : Finset (Fin n)}
    {α : Fin n → ℝ} :
    α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C ↔
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C ∧
        α ∈ facet_defining_liftings_of_cover_inequality
          (fun j ↦ (weights j : ℝ))
          (capacity : ℝ)
          C :=
  Iff.rfl

/-- Helper for Remark 7.5: every valid lifting already agrees with the remark coefficient vector
on the cover coordinates. -/
private theorem eqOnCoverOfMemValidLiftings
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    {α : Fin n → ℝ}
    (hα : α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C)
    {j : Fin n}
    (hj : j ∈ C) :
    α j = remark_7_5_lifting_coeff C h j := by
  have hcover : α j = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hα).1 j hj
  -- Both sides normalize to the base cover coefficient `1`.
  simpa [remark_7_5_lifting_coeff_apply_of_mem hj] using hcover

/-- Helper for Remark 7.5: the Theorem 7.4 context supplies the minimal-cover structure together
with the base cover validity and restricted-facet facts used by the sequential lifting route. -/
private theorem remark_7_5_baseFacetData
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam) :
    IsMinimalKnapsackCover weights capacity C ∧
      is_valid_inequality
        (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
        (cover_indicator C)
        (cover_inequality_rhs C) ∧
      facet_defining_inequality
        (cover_restricted_polytope weights capacity C)
        (cover_indicator C)
        (cover_inequality_rhs C) := by
  rcases hctx with ⟨_, _, _, _, _, hweights_le, hCmin, _, _⟩
  have hcover : IsKnapsackCover weights capacity C := inferInstance
  refine ⟨hCmin, ?_, ?_⟩
  · -- Every knapsack cover inequality is valid on the ambient knapsack polytope.
    exact coverInequality_validOnKnapsackPolytope weights capacity C hcover
  · -- Minimality upgrades the restricted cover face to the facet-defining owner.
    exact
      (cover_inequality_facet_defining_iff_minimal_cover
        weights capacity hweights_le C hcover).2 hCmin

/-- Helper for Remark 7.5: validity on the binary knapsack set transfers unchanged to its convex
hull, namely the public knapsack polytope owner. -/
private theorem remark_7_5_polytopeValid_of_setValid
    (a : Fin n → ℝ)
    (b : ℝ)
    (α : Fin n → ℝ)
    (β : ℝ)
    (hvalid : is_valid_inequality (zero_one_knapsack_set a b) α β) :
    is_valid_inequality (zero_one_knapsack_polytope a b) α β := by
  -- The polytope is defined as the convex hull of the binary feasible set.
  rw [zero_one_knapsack_polytope_eq_convexHull]
  exact (is_valid_inequality_convexHull_iff).2 hvalid

/-- Helper for Remark 7.5: under the strengthened upper bound, every valid lifting coefficient at
an off-cover index is bounded above by the prescribed interval index. -/
private theorem remark_7_5_coeff_le_of_mem_validLifting
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {α : Fin n → ℝ}
    (hα : α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C)
    {j : Fin n}
    (hj : j ∉ C) :
    α j ≤ h j := by
  rcases hctx with ⟨t, ht, rfl, hdescending, hweights_pos, hweights_le, hCmin, rfl, rfl⟩
  have hα_cover :
      ∀ i ∈ remark_7_5_cover (n := n) t, α i = 1 :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hα).1
  have hαvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (remark_7_5_cover (n := n) t)) :=
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp hα).2
  -- First move the valid inequality from the convex hull back to the binary knapsack set.
  have hαvalid_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        α
        (cover_inequality_rhs (remark_7_5_cover (n := n) t)) := by
    rw [zero_one_knapsack_polytope_eq_convexHull] at hαvalid_poly
    exact (is_valid_inequality_convexHull_iff.mp hαvalid_poly)
  by_cases hs : h j + 1 ≤ t
  · let suffix : Finset (Fin n) :=
      (remark_7_5_cover (n := n) t).filter (fun i : Fin n ↦ h j + 1 ≤ (i : ℕ))
    let x : Fin n → ℝ := cover_indicator suffix + Pi.single j (1 : ℝ)
    have hj_suffix : j ∉ suffix := by
      intro hj'
      exact hj ((Finset.mem_filter.mp hj').1)
    -- The suffix witness is binary and uses exactly the last `t - (h j + 1)` cover indices plus
    -- the off-cover variable `j`.
    have hx_mem : x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
      rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        by_cases hij : i = j
        · subst hij
          right
          simp [x, cover_indicator, hj_suffix]
        · by_cases hi_suffix : i ∈ suffix
          · right
            simp [x, cover_indicator, hi_suffix, hij]
          · left
            simp [x, cover_indicator, hi_suffix, hij]
      · have hupperj : weights j ≤ remark_7_5_mu weights t ht (h j + 1) -
            remark_7_5_cover_excess weights capacity t ht :=
          hupper j hj
        have hsuffix_sum :
            suffix.sum weights =
              remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht (h j + 1) := by
          simpa [suffix] using
            remark_7_5_cover_suffix_sum_eq weights t ht (h j + 1) hs
        have hsuffix_le_capacity :
            suffix.sum weights ≤ capacity := by
          have ht_pos : 0 < t := Nat.lt_of_lt_of_le (Nat.succ_pos _) hs
          let r0 : Fin t := ⟨0, ht_pos⟩
          have hr0_mem : r0.castLE ht ∈ remark_7_5_cover (n := n) t := by
            simp [remark_7_5_cover]
          have hsuffix_subset :
              suffix ⊆ (remark_7_5_cover (n := n) t).erase (r0.castLE ht) := by
            intro i hi
            refine Finset.mem_erase.mpr ?_
            constructor
            · intro hir0
              have hi_ge : h j + 1 ≤ (i : ℕ) := (Finset.mem_filter.mp hi).2
              have hir0_zero : (i : ℕ) = 0 := congrArg Fin.val hir0
              omega
            · exact (Finset.mem_filter.mp hi).1
          have hsuffix_le_erase :
              suffix.sum weights ≤
                ((remark_7_5_cover (n := n) t).erase (r0.castLE ht)).sum weights :=
            Finset.sum_le_sum_of_subset_of_nonneg hsuffix_subset (by
              intro i hi hino
              exact Nat.zero_le _)
          exact le_trans hsuffix_le_erase (hCmin.erase_sum_le (r0.castLE ht) hr0_mem)
        have hweight_nat :
            weights j + suffix.sum weights ≤ capacity := by
          have hlam_le_mu :
              remark_7_5_mu weights t ht t - capacity ≤
                remark_7_5_mu weights t ht (h j + 1) := by
            rw [hsuffix_sum] at hsuffix_le_capacity
            omega
          have hupperj' :
              weights j ≤
                remark_7_5_mu weights t ht (h j + 1) -
                  (remark_7_5_mu weights t ht t - capacity) := by
            simpa [remark_7_5_cover_excess] using hupperj
          have hupperj_add :
              weights j + (remark_7_5_mu weights t ht t - capacity) ≤
                remark_7_5_mu weights t ht (h j + 1) :=
            (Nat.le_sub_iff_add_le hlam_le_mu).mp hupperj'
          have hmu_t_ge_capacity :
              capacity ≤ remark_7_5_mu weights t ht t := by
            have hcover : IsKnapsackCover weights capacity (remark_7_5_cover (n := n) t) :=
              inferInstance
            have hcover_lt :
                capacity < (remark_7_5_cover (n := n) t).sum weights :=
              (isKnapsackCover_iff weights capacity (remark_7_5_cover (n := n) t)).mp hcover
            rw [remark_7_5_cover_sum_eq_mu weights t ht] at hcover_lt
            exact Nat.le_of_lt hcover_lt
          have hupperj_total :
              weights j + remark_7_5_mu weights t ht t ≤
                remark_7_5_mu weights t ht (h j + 1) + capacity := by
            have hupperj_add_capacity := Nat.add_le_add_right hupperj_add capacity
            calc
              weights j + remark_7_5_mu weights t ht t
                  = weights j +
                      ((remark_7_5_mu weights t ht t - capacity) + capacity) := by
                        rw [Nat.sub_add_cancel hmu_t_ge_capacity]
              _ = (weights j + (remark_7_5_mu weights t ht t - capacity)) + capacity := by
                    omega
              _ ≤ remark_7_5_mu weights t ht (h j + 1) + capacity := hupperj_add_capacity
          have hmu_prefix_le :
              remark_7_5_mu weights t ht (h j + 1) ≤ remark_7_5_mu weights t ht t := by
            have hs_le_n : h j + 1 ≤ n := Nat.le_trans hs ht
            have hprefix_sum_le :
                (remark_7_5_cover (n := n) (h j + 1)).sum weights ≤
                  (remark_7_5_cover (n := n) t).sum weights :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (remark_7_5_cover_subset (n := n) hs)
                (by
                  intro i hi hino
                  exact Nat.zero_le _)
            have hprefix_sum_eq :
                (remark_7_5_cover (n := n) (h j + 1)).sum weights =
                  remark_7_5_mu weights t ht (h j + 1) := by
              calc
                (remark_7_5_cover (n := n) (h j + 1)).sum weights
                    = remark_7_5_mu weights (h j + 1) hs_le_n (h j + 1) := by
                        rw [remark_7_5_cover_sum_eq_mu]
                _ = remark_7_5_mu weights t ht (h j + 1) := by
                      rw [remark_7_5_mu_prefix_eq weights hs_le_n ht hs]
            have hcover_sum_eq :
                (remark_7_5_cover (n := n) t).sum weights =
                  remark_7_5_mu weights t ht t := by
              rw [remark_7_5_cover_sum_eq_mu]
            rw [hprefix_sum_eq, hcover_sum_eq] at hprefix_sum_le
            exact hprefix_sum_le
          have hmu_split :
              remark_7_5_mu weights t ht t =
                remark_7_5_mu weights t ht (h j + 1) + suffix.sum weights := by
            rw [hsuffix_sum]
            omega
          have hweight_nat' :
              weights j + suffix.sum weights ≤
                capacity := by
            have hcombined :
                weights j + suffix.sum weights +
                    remark_7_5_mu weights t ht (h j + 1) ≤
                  remark_7_5_mu weights t ht (h j + 1) + capacity := by
              calc
                weights j + suffix.sum weights +
                    remark_7_5_mu weights t ht (h j + 1)
                    = weights j + remark_7_5_mu weights t ht t := by
                        rw [hmu_split]
                        omega
                _ ≤ remark_7_5_mu weights t ht (h j + 1) + capacity := hupperj_total
            omega
          exact hweight_nat'
        -- The witness weight is the suffix sum plus the pivot weight.
        have hx_weight :
            ∑ i, (weights i : ℝ) * x i = (weights j + suffix.sum weights : ℝ) := by
          calc
            ∑ i, (weights i : ℝ) * x i
                = (fun i ↦ (weights i : ℝ)) ⬝ᵥ x := by
                    simp [dotProduct]
            _ = x ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by rw [dotProduct_comm]
            _ = (cover_indicator suffix + Pi.single j (1 : ℝ)) ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by
                    simp [x]
            _ = cover_indicator suffix ⬝ᵥ (fun i ↦ (weights i : ℝ)) +
                  Pi.single j (1 : ℝ) ⬝ᵥ (fun i ↦ (weights i : ℝ)) := by
                    rw [add_dotProduct]
            _ = (suffix.sum fun i ↦ (weights i : ℝ)) + weights j := by
                    rw [coverIndicator_dot_eq_sum]
                    simp
            _ = (weights j + suffix.sum weights : ℝ) := by
                    rw [Nat.cast_sum]
                    norm_num [add_comm]
        rw [hx_weight]
        exact_mod_cast hweight_nat
    have hx_valid := hαvalid_set hx_mem
    have hsuffix_card :
        suffix.card = t - (h j + 1) := by
      simpa [suffix] using
        remark_7_5_cover_suffix_card (n := n) t (h j + 1) ht hs
    have hsuffix_dot :
        α ⬝ᵥ x = (suffix.card : ℝ) + α j := by
      have hsuffix_sum_one :
          suffix.sum α = suffix.sum (fun _ ↦ (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hα_cover i ((Finset.mem_filter.mp hi).1)
      calc
        α ⬝ᵥ x
            = α ⬝ᵥ (cover_indicator suffix + Pi.single j (1 : ℝ)) := by
                simp [x]
        _ = α ⬝ᵥ cover_indicator suffix + α ⬝ᵥ Pi.single j (1 : ℝ) := by
                rw [dotProduct_add]
        _ = cover_indicator suffix ⬝ᵥ α + α j := by
                rw [dotProduct_comm]
                simp [dotProduct_comm]
        _ = suffix.sum α + α j := by
                rw [coverIndicator_dot_eq_sum]
        _ = (suffix.card : ℝ) + α j := by
                rw [hsuffix_sum_one]
                simp
    have hcover_rhs :
        cover_inequality_rhs (remark_7_5_cover (n := n) t) = (t : ℝ) - 1 := by
      rw [cover_inequality_rhs_eq, remark_7_5_cover_card (n := n) t ht]
    have hsuffix_card_real :
        (suffix.card : ℝ) = (t : ℝ) - ((h j + 1 : ℕ) : ℝ) := by
      rw [hsuffix_card, Nat.cast_sub hs]
    -- The witness saturates the last `t - (h j + 1)` cover coefficients, so validity bounds `α j`
    -- by the remaining slack `h j`.
    rw [hsuffix_dot, hcover_rhs, hsuffix_card_real] at hx_valid
    norm_num at hx_valid
    linarith
  · have ht_le_hj : t ≤ h j := by
      omega
    let x : Fin n → ℝ := Pi.single j (1 : ℝ)
    -- If `h j` is already beyond the cover length, the singleton point at `j` gives the bound.
    have hx_mem : x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
      rw [mem_zero_one_knapsack_set_iff]
      constructor
      · intro i
        by_cases hij : i = j
        · right
          subst hij
          simp [x]
        · left
          simp [x, hij]
      · have hx_weight : ∑ i, (weights i : ℝ) * x i = weights j := by
          calc
            ∑ i, (weights i : ℝ) * x i = (fun i ↦ (weights i : ℝ)) ⬝ᵥ x := by
              simp [dotProduct]
            _ = (fun i ↦ (weights i : ℝ)) ⬝ᵥ Pi.single j (1 : ℝ) := by
              simp [x]
            _ = weights j := by
              simp
        rw [hx_weight]
        exact_mod_cast hweights_le j
    have hx_valid := hαvalid_set hx_mem
    have hcover_rhs :
        cover_inequality_rhs (remark_7_5_cover (n := n) t) = (t : ℝ) - 1 := by
      rw [cover_inequality_rhs_eq, remark_7_5_cover_card (n := n) t ht]
    have ht_le_hj_real : (t : ℝ) ≤ h j := by
      exact_mod_cast ht_le_hj
    rw [hcover_rhs] at hx_valid
    simp [x] at hx_valid
    linarith

/-- Helper for Remark 7.5: isolating a pivot coordinate rewrites the knapsack weight sum as the
pivot contribution plus the sum over the remaining `succAbove` coordinates. -/
private theorem remark_7_5_weightedSum_insertNth
    (j : Fin (n + 1))
    (weights : Fin (n + 1) → ℕ)
    (xj : ℝ)
    (y : Fin n → ℝ) :
    ∑ i, (weights i : ℝ) * (@Fin.insertNth _ (fun _ ↦ ℝ) j xj y) i =
      (weights j : ℝ) * xj + ∑ i : Fin n, (weights (j.succAbove i) : ℝ) * y i := by
  -- Split the full sum into the pivot term and the remaining `succAbove` coordinates once.
  let z : Fin (n + 1) → ℝ := @Fin.insertNth _ (fun _ ↦ ℝ) j xj y
  simpa [z, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using
    (Fin.sum_univ_succAbove
      (fun i : Fin (n + 1) ↦ (weights i : ℝ) * z i) j)

/-- Helper for Remark 7.5: after reindexing by a pivot `j`, binary knapsack membership is exactly
the binary conditions on the pivot and the `succAbove` coordinates together with the transported
capacity inequality. -/
private theorem remark_7_5_mem_zero_one_knapsack_set_insertNth_iff
    (j : Fin (n + 1))
    (weights : Fin (n + 1) → ℕ)
    (capacity : ℕ)
    (xj : ℝ)
    (y : Fin n → ℝ) :
    (@Fin.insertNth _ (fun _ ↦ ℝ) j xj y) ∈
        zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ↔
      (xj = 0 ∨ xj = 1) ∧
        (∀ i : Fin n, y i = 0 ∨ y i = 1) ∧
        (weights j : ℝ) * xj +
            ∑ i : Fin n, (weights (j.succAbove i) : ℝ) * y i ≤
          (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff, remark_7_5_weightedSum_insertNth]
  constructor
  · intro hx
    refine ⟨?_, ?_, hx.2⟩
    · simpa [Fin.insertNth_apply_same] using hx.1 j
    -- The non-pivot coordinates are exactly the `succAbove` coordinates of the inserted tuple.
    intro i
    simpa [Fin.insertNth_apply_succAbove] using hx.1 (j.succAbove i)
  · rintro ⟨hxj, hy, hweight⟩
    refine ⟨?_, hweight⟩
    -- Reassemble the full binary tuple from the pivot coordinate and the transported complement.
    exact (Fin.forall_iff_succAbove j).2
      ⟨by simpa [Fin.insertNth_apply_same] using hxj,
        fun i ↦ by simpa [Fin.insertNth_apply_succAbove] using hy i⟩

/-- Helper for Remark 7.5: every binary knapsack point already lies in the ambient zero-one owner
used by Proposition 7.2. -/
private theorem remark_7_5_zeroOneKnapsackSet_subset_zeroOnePointsUniv
    (weights : Fin n → ℕ)
    (capacity : ℕ) :
    zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ⊆
      zero_one_points (Nat.le_refl n) (Set.univ : Set (Fin n → ℝ)) := by
  intro x hx
  rw [mem_zero_one_points_iff]
  rw [mem_zero_one_knapsack_set_iff] at hx
  constructor
  · simp
  · simpa using hx.1

/-- Helper for Remark 7.5: once the ambient prefix has passed the cover length `t`, the next stage
coefficient vector is the previous-stage coefficient vector with the new last coefficient appended.
-/
private theorem remark_7_5_liftingCoeff_snoc
    {m t : ℕ}
    (ht : t ≤ m)
    (h : Fin (m + 1) → ℕ) :
    remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h =
      Fin.snoc
        (remark_7_5_lifting_coeff (remark_7_5_cover (n := m) t)
          (fun i : Fin m ↦ h i.castSucc))
        (h (Fin.last m)) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
  · -- On the old coordinates, the cover-membership test is unchanged by `castSucc`.
    by_cases hj : j ∈ remark_7_5_cover (n := m) t
    · have hj' : j.castSucc ∈ remark_7_5_cover (n := m + 1) t := by
        exact remark_7_5_cover_mem_iff.mpr (by simpa using (remark_7_5_cover_mem_iff.mp hj))
      simp [remark_7_5_lifting_coeff, hj, hj']
    · have hj' : j.castSucc ∉ remark_7_5_cover (n := m + 1) t := by
        intro hj''
        exact hj (remark_7_5_cover_mem_iff.mpr (by simpa using (remark_7_5_cover_mem_iff.mp hj'')))
      simp [remark_7_5_lifting_coeff, hj, hj']
  · -- The new last coordinate is off the cover because `t ≤ m`.
    simp [remark_7_5_lifting_coeff, remark_7_5_cover, Nat.not_lt.mpr ht]

/-- Helper for Remark 7.5: validity on the previous prefix stage transfers directly to the zero
slice `x_last = 0` when the next variable is already the literal last coordinate. -/
private theorem remark_7_5_lastCoordinateZeroSliceValid
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
    · -- The zero slice deletes the last-coordinate term from the knapsack weight sum.
      simpa [Fin.sum_univ_castSucc, hxlast0] using hxS.2
  have hy_valid := hvalid hy_mem
  -- The lifted coefficient vector restricts to the old stage because the last coordinate vanishes.
  calc
    Fin.snoc α 0 ⬝ᵥ x = partial_lifting_value α x + 0 * x (Fin.last m) := by
      rw [dotProduct_last_coordinate_lifting_coeffs]
    _ = α ⬝ᵥ (fun i : Fin m ↦ x i.castSucc) := by
      simp [partial_lifting_value, dotProduct, hxlast0]
    _ ≤ β := hy_valid

/-- Helper for Remark 7.5: once the zero slice is valid and the one slice satisfies the direct
partial-value bound `partial_lifting_value α x ≤ β - γ`, the coefficient `γ` yields a valid
lifted inequality on the whole binary knapsack set. -/
private theorem remark_7_5_valid_of_zeroSlice_and_oneSliceBound
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (α : Fin m → ℝ)
    (β γ : ℝ)
    (hzero :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
          last_coordinate_eq_set m 0)
        (Fin.snoc α 0)
        β)
    (hone :
      ∀ x : Fin (m + 1) → ℝ,
        x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) →
          x (Fin.last m) = 1 →
            partial_lifting_value α x ≤ β - γ) :
    is_valid_inequality
      (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
      (Fin.snoc α γ)
      β := by
  intro x hx
  rw [mem_zero_one_knapsack_set_iff] at hx
  rcases hx.1 (Fin.last m) with hxlast0 | hxlast1
  · -- On the zero slice, the new coefficient vanishes and the old validity applies verbatim.
    have hx_zero :
        x ∈
          zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
            last_coordinate_eq_set m 0 := by
      exact ⟨by simpa [mem_zero_one_knapsack_set_iff] using hx,
        mem_last_coordinate_eq_set_iff.mpr hxlast0⟩
    have hzero_valid := hzero hx_zero
    calc
      Fin.snoc α γ ⬝ᵥ x = Fin.snoc α 0 ⬝ᵥ x := by
        rw [dotProduct_last_coordinate_lifting_coeffs, dotProduct_last_coordinate_lifting_coeffs]
        simp [hxlast0]
      _ ≤ β := hzero_valid
  · -- On the one slice, the supplied partial-value bound is exactly the missing slack.
    have hone_bound :
        partial_lifting_value α x ≤ β - γ :=
      hone x (by simpa [mem_zero_one_knapsack_set_iff] using hx) hxlast1
    calc
      Fin.snoc α γ ⬝ᵥ x = partial_lifting_value α x + γ := by
        rw [dotProduct_last_coordinate_lifting_coeffs, hxlast1]
        ring
      _ ≤ β := by linarith [hone_bound]

/-- Helper for Remark 7.5: the singleton point at the literal last coordinate is always a feasible
binary knapsack point when every individual weight is at most the capacity. -/
private theorem remark_7_5_lastSingletonFeasible
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (hweights_le : ∀ j, weights j ≤ capacity) :
    Pi.single (Fin.last m) (1 : ℝ) ∈
      zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    by_cases hi : i = Fin.last m
    · right
      subst hi
      simp
    · left
      simp [hi]
  · -- The singleton weight is exactly the last item weight, which is feasible by hypothesis.
    let x : Fin (m + 1) → ℝ := Pi.single (Fin.last m) (1 : ℝ)
    have hweight :
        ∑ i, (weights i : ℝ) * x i =
          weights (Fin.last m) := by
      calc
        ∑ i, (weights i : ℝ) * x i
            = (fun i ↦ (weights i : ℝ)) ⬝ᵥ x := by
                simp [dotProduct, x]
        _ = weights (Fin.last m) * 1 := by
              simp [x]
        _ = weights (Fin.last m) := by ring
    rw [hweight]
    exact_mod_cast hweights_le (Fin.last m)

/-- Helper for Remark 7.5: at the full-cover stage, the remark coefficient vector is just the
cover indicator of the ambient `Finset.univ`. -/
private theorem remark_7_5_univCoverCoeff_eq_coverIndicator
    (h : Fin n → ℕ) :
    remark_7_5_lifting_coeff (remark_7_5_cover (n := n) n) h =
      cover_indicator Finset.univ := by
  have huniv : remark_7_5_cover (n := n) n = Finset.univ := by
    ext i
    simp [remark_7_5_cover_mem_iff]
  funext i
  simp [huniv, remark_7_5_lifting_coeff, cover_indicator]

/-- Helper for Remark 7.5: applying the generic cover-coefficient constructor to the already
normalized Remark 7.5 coefficient vector leaves it unchanged. -/
private theorem remark_7_5_liftingCoeff_idempotent
    (C : Finset (Fin n))
    (h : Fin n → ℕ) :
    lifted_cover_inequality_coeff C (remark_7_5_lifting_coeff C h) =
      remark_7_5_lifting_coeff C h := by
  -- Both coefficient vectors are determined by the same cover-membership split.
  funext i
  by_cases hi : i ∈ C
  · simp [lifted_cover_inequality_coeff, hi]
  · simp [lifted_cover_inequality_coeff, remark_7_5_lifting_coeff, hi]

/-- Helper for Remark 7.5: a nonempty equality face exposed by a coefficient having a unit
coordinate has affine dimension at most one below the ambient coordinate dimension. -/
private theorem remark_7_5_faceSet_finrank_add_one_le
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
    -- Differences of two points in the equality hyperplane annihilate its exposing functional.
    intro v hv
    rw [LinearMap.mem_ker]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀span] at hv
    rcases hv with ⟨x, hxspan, rfl⟩
    have hxEq : c ⬝ᵥ x = β := hspanSubset hxspan
    have hx₀Eq : c ⬝ᵥ x₀ = β := (mem_face_set_iff.mp hx₀).2
    simp [dotProductStrongDual_apply, vsub_eq_sub, hxEq, hx₀Eq]
  have hsurjective : Function.Surjective (dotProductStrongDual c).toLinearMap := by
    -- The unit coordinate gives an explicit preimage of every scalar.
    intro y
    refine ⟨y • Pi.single j (1 : ℝ), ?_⟩
    simp [dotProductStrongDual_apply, dotProduct, Pi.single_apply, hcj]
  have hrange : LinearMap.range (dotProductStrongDual c).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  have hrangeFinrank :
      Module.finrank ℝ (LinearMap.range (dotProductStrongDual c).toLinearMap) = 1 := by
    rw [hrange, finrank_top]
    simp
  have hrankNull :=
    LinearMap.finrank_range_add_finrank_ker (dotProductStrongDual c).toLinearMap
  have hkernelFinrank :
      Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 = n := by
    rw [hrangeFinrank] at hrankNull
    simpa [Module.finrank_fintype_fun_eq_card, add_comm] using hrankNull
  calc
    Module.finrank ℝ (affineSpan ℝ (face_set P c β)).direction + 1
        ≤ Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_mono hdirection) 1
    _ = n := hkernelFinrank

/-- Helper for Remark 7.5: in the base stage `C = univ`, the remark coefficient vector cuts out
the same facet as the minimal cover inequality on the ambient knapsack polytope. -/
private theorem remark_7_5_univCoverFacetMembership
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (h : Fin n → ℕ)
    (hctx :
      remark_7_5_theorem_7_4_context
        weights
        capacity
        (remark_7_5_cover (n := n) n)
        (remark_7_5_mu weights n (Nat.le_refl n))
        (remark_7_5_cover_excess weights capacity n (Nat.le_refl n))) :
    remark_7_5_lifting_coeff (remark_7_5_cover (n := n) n) h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        (remark_7_5_cover (n := n) n) := by
  have hbase :=
    remark_7_5_baseFacetData
      weights
      capacity
      (remark_7_5_cover (n := n) n)
      (remark_7_5_mu weights n (Nat.le_refl n))
      (remark_7_5_cover_excess weights capacity n (Nat.le_refl n))
      hctx
  rcases hctx with ⟨_, _, _, _, _, hweights_le, hCmin, _, _⟩
  have hn_two : 2 ≤ n := by
    simpa [remark_7_5_cover_card (n := n) n (Nat.le_refl n)] using
      cover_card_ge_two
        weights
        capacity
        hweights_le
        (remark_7_5_cover (n := n) n)
        hCmin.toIsKnapsackCover
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn_two
  rcases Nat.exists_eq_succ_of_ne_zero hn_pos.ne' with ⟨m, rfl⟩
  let C : Finset (Fin (m + 1)) := remark_7_5_cover (n := m + 1) (m + 1)
  let coeff : Fin (m + 1) → ℝ := cover_indicator C
  let P : Set (Fin (m + 1) → ℝ) :=
    zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ)
  let F : Set (Fin (m + 1) → ℝ) := face_set P coeff (cover_inequality_rhs C)
  have hC_univ : C = Finset.univ := by
    ext i
    constructor
    · intro hi
      simp
    · intro hi
      exact remark_7_5_cover_mem_iff.mpr i.isLt
  have hcoeff_eq :
      remark_7_5_lifting_coeff C h = coeff := by
    rw [remark_7_5_univCoverCoeff_eq_coverIndicator]
    exact congrArg cover_indicator hC_univ.symm
  have hvalidHull :
      is_valid_inequality P coeff (cover_inequality_rhs C) := by
    simpa [P, coeff, C] using hbase.2.1
  have hp_mem :
      ∀ j : Fin (m + 1), omitPoint C j ∈ F := by
    intro j
    have hj : j ∈ C := by
      simpa [C, remark_7_5_cover_mem_iff] using j.isLt
    refine (mem_face_set_iff).2 ⟨?_, ?_⟩
    · simpa [P] using
        (subset_convexHull
          ℝ
          (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
          (omitPoint_mem_zeroOneKnapsackSet weights capacity C hCmin hj))
    · simpa [coeff, coverIndicator_dot_eq_sum] using omitPoint_coverSum_eq_rhs C hj
  let p : Fin (m + 1) → Fin (m + 1) → ℝ := fun j ↦ omitPoint C j
  have hp_aff : AffineIndependent ℝ p := by
    rw [affineIndependent_iff_linearIndependent_tail_sub p]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hcoord := congrArg (fun x : Fin (m + 1) → ℝ ↦ x i.succ) hg
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, omitPoint, Finset.mem_erase,
      ne_eq, Fin.succ_inj, remark_7_5_cover_mem_iff, Fin.val_succ, Order.lt_add_one_iff,
      Order.add_one_le_iff, Fin.is_lt, and_true, ite_not, Fin.succ_ne_zero, not_false_eq_true,
      and_self, ↓reduceIte, smul_eq_mul, Pi.zero_apply, p, C] at hcoord
    rw [Fintype.sum_eq_single i] at hcoord
    · simpa using hcoord
    · intro j hji
      simp [Ne.symm hji]
  have hF_nonempty : F.Nonempty := ⟨p 0, hp_mem 0⟩
  have hF_exposed : IsExposed ℝ P F := by
    simpa [F, P] using isExposed_face_set_of_valid_inequality hvalidHull
  have hdir_lower :
      m ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    let u : Fin m → Fin (m + 1) → ℝ := fun i ↦ p i.succ - p 0
    have hu_dir :
        ∀ i : Fin m, u i ∈ (affineSpan ℝ F).direction := by
      intro i
      exact
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ F (hp_mem i.succ))
          (subset_affineSpan ℝ F (hp_mem 0))
    have hspan_le :
        Submodule.span ℝ (Set.range u) ≤ (affineSpan ℝ F).direction := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hu_dir i
    have hu_lin : LinearIndependent ℝ u := by
      simpa [u] using (affineIndependent_iff_linearIndependent_tail_sub p).mp hp_aff
    have hspan_finrank :
        Module.finrank ℝ (Submodule.span ℝ (Set.range u)) = m := by
      simpa [u] using finrank_span_eq_card (R := ℝ) (b := u) hu_lin
    simpa [hspan_finrank] using Submodule.finrank_mono hspan_le
  have hdir_le :
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ m := by
    have hcoeffZero : coeff 0 = 1 := by
      simp [coeff, C, cover_indicator]
    have hcodim :=
      remark_7_5_faceSet_finrank_add_one_le
        (P := P)
        (c := coeff)
        (β := cover_inequality_rhs C)
        0
        hcoeffZero
        hF_nonempty
    have hcodim' : Module.finrank ℝ (affineSpan ℝ F).direction + 1 ≤ m + 1 := by
      simpa [F] using hcodim
    omega
  have hF_codim :
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ P).direction := by
    have hF_dim : Module.finrank ℝ (affineSpan ℝ F).direction = m :=
      le_antisymm hdir_le hdir_lower
    have hP_dim : Module.finrank ℝ (affineSpan ℝ P).direction = m + 1 := by
      have hover :
          zero_one_knapsack_overweight_indices
              (fun j ↦ (weights j : ℝ))
              (capacity : ℝ) = ∅ := by
        ext j
        simp [zero_one_knapsack_overweight_indices, hweights_le j]
      simpa [P, hover] using
        (zero_one_knapsack_polytope_finrank_direction_affineSpan
          (fun j ↦ (weights j : ℝ))
          (capacity : ℝ)
          (fun j ↦ by positivity)
          (by positivity))
    rw [hF_dim, hP_dim]
  refine (mem_facet_defining_liftings_of_cover_inequality_iff).2 ?_
  rw [lifted_cover_face, remark_7_5_liftingCoeff_idempotent, hcoeff_eq]
  simpa [F, P] using (isFacetOf_iff).2 ⟨hF_nonempty, hF_exposed, hF_codim⟩

/-- Helper for Remark 7.5: once the cover is already the whole index set, the displayed
coefficient vector is valid on the binary knapsack set because it is exactly the base cover
inequality. -/
private theorem remark_7_5_univCoverSetValid
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (h : Fin n → ℕ)
    (hctx :
      remark_7_5_theorem_7_4_context
        weights
        capacity
        (remark_7_5_cover (n := n) n)
        (remark_7_5_mu weights n (Nat.le_refl n))
        (remark_7_5_cover_excess weights capacity n (Nat.le_refl n))) :
    is_valid_inequality
      (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff (remark_7_5_cover (n := n) n) h)
      (cover_inequality_rhs (remark_7_5_cover (n := n) n)) := by
  have hbase :=
    remark_7_5_baseFacetData
      weights
      capacity
      (remark_7_5_cover (n := n) n)
      (remark_7_5_mu weights n (Nat.le_refl n))
      (remark_7_5_cover_excess weights capacity n (Nat.le_refl n))
      hctx
  have hcover_eq :
      cover_indicator (remark_7_5_cover (n := n) n) =
        cover_indicator Finset.univ := by
    have huniv : remark_7_5_cover (n := n) n = Finset.univ := by
      ext i
      simp [remark_7_5_cover_mem_iff]
    simp [huniv]
  have hcoeff_eq :
      remark_7_5_lifting_coeff (remark_7_5_cover (n := n) n) h =
        cover_indicator Finset.univ := by
    exact remark_7_5_univCoverCoeff_eq_coverIndicator h
  intro x hx
  have hxpoly :
      x ∈ zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ) := by
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact subset_convexHull ℝ _ hx
  simpa [hcoeff_eq, hcover_eq] using hbase.2.1 hxpoly

/-- Helper for Remark 7.5: after deleting an off-cover last coordinate, the shorter prefix cover is
exactly the `castSucc` image of the previous one. -/
private theorem remark_7_5_cover_eq_castSuccImage
    {m t : ℕ}
    (ht : t ≤ m) :
    remark_7_5_cover (n := m + 1) t =
      (remark_7_5_cover (n := m) t).map
        ⟨fun i : Fin m ↦ i.castSucc, by
          intro a b hab
          exact Fin.castSucc_injective _ hab
        ⟩ := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
  · simp [remark_7_5_cover_mem_iff]
  · simp [remark_7_5_cover, Nat.not_lt.mpr ht]

/-- Helper for Remark 7.5: erasing a prefix-cover coordinate commutes with passing to the
`castSucc` image. -/
private theorem remark_7_5_cover_erase_eq_castSuccImage
    {m t : ℕ}
    (ht : t ≤ m)
    {j : Fin m} :
    ((remark_7_5_cover (n := m) t).erase j).map
        ⟨fun i : Fin m ↦ i.castSucc, by
          intro a b hab
          exact Fin.castSucc_injective _ hab
        ⟩ =
      (remark_7_5_cover (n := m + 1) t).erase j.castSucc := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with (⟨k, rfl⟩ | rfl)
  · simp [remark_7_5_cover_mem_iff]
  · simp [remark_7_5_cover, Nat.not_lt.mpr ht]

/-- Helper for Remark 7.5: summing the prefix cover after deleting an off-cover last coordinate is
unchanged by passing to the shorter `castSucc`-indexed stage. -/
private theorem remark_7_5_coverSum_castSucc_eq
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ) :
    (remark_7_5_cover (n := m) t).sum (fun i : Fin m ↦ weights i.castSucc) =
      (remark_7_5_cover (n := m + 1) t).sum weights := by
  -- Package the `castSucc` transport once at the sum level instead of reopening `Finset.map`.
  rw [remark_7_5_cover_eq_castSuccImage ht, Finset.sum_map]
  rfl

/-- Helper for Remark 7.5: erasing a prefix-cover coordinate and summing the remaining weights is
also stable under the `castSucc` transport. -/
private theorem remark_7_5_coverEraseSum_castSucc_eq
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    {j : Fin m} :
    (((remark_7_5_cover (n := m + 1) t).erase j.castSucc).sum weights) =
      (((remark_7_5_cover (n := m) t).erase j).sum fun i : Fin m ↦ weights i.castSucc) := by
  -- The erase transport uses the same `castSucc` image, so the transported sums coincide.
  rw [← remark_7_5_cover_erase_eq_castSuccImage (m := m) (t := t) ht (j := j), Finset.sum_map]
  rfl

/-- Helper for Remark 7.5: the prefix partial sums are unchanged when the ambient index set is
extended by one off-cover last coordinate. -/
private theorem remark_7_5_mu_castSucc_eq
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ) :
    remark_7_5_mu (fun i : Fin m ↦ weights i.castSucc) t ht =
      remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) := by
  funext s
  unfold remark_7_5_mu
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  by_cases hlt : ℓ < t
  · simp [hlt]
  · simp [hlt]

/-- Helper for Remark 7.5: the cover excess is unchanged when an off-cover last coordinate is
deleted from the ambient stage. -/
private theorem remark_7_5_coverExcess_castSucc_eq
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ) :
    remark_7_5_cover_excess
        (fun i : Fin m ↦ weights i.castSucc)
        capacity
        t
        ht =
      remark_7_5_cover_excess
        weights
        capacity
        t
        (Nat.le_trans ht (Nat.le_succ m)) := by
  -- Both cover excesses are defined from the same transported prefix partial sums.
  simp [remark_7_5_cover_excess, remark_7_5_mu_castSucc_eq ht weights]

/-- Helper for Remark 7.5: the prefix minimal-cover structure survives after deleting an
off-cover last coordinate. -/
private theorem remark_7_5_minimalCover_castSucc
    {m t : ℕ}
    (capacity : ℕ)
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := m + 1) t)) :
    IsMinimalKnapsackCover
      (fun i : Fin m ↦ weights i.castSucc)
      capacity
      (remark_7_5_cover (n := m) t) := by
  refine (isMinimalKnapsackCover_iff _ _ _).2 ?_
  constructor
  · rw [isKnapsackCover_iff]
    have hsum_eq :
        (remark_7_5_cover (n := m) t).sum (fun i : Fin m ↦ weights i.castSucc) =
          (remark_7_5_cover (n := m + 1) t).sum weights := by
      exact remark_7_5_coverSum_castSucc_eq ht weights
    have hcover :
        capacity < (remark_7_5_cover (n := m + 1) t).sum weights :=
      (isKnapsackCover_iff weights capacity
        (remark_7_5_cover (n := m + 1) t)).mp hCmin.toIsKnapsackCover
    simpa [hsum_eq] using hcover
  · intro j hj
    have hj' : j.castSucc ∈ remark_7_5_cover (n := m + 1) t := by
      simpa [remark_7_5_cover_mem_iff] using hj
    have herase := hCmin.erase_sum_le j.castSucc hj'
    simpa [remark_7_5_coverEraseSum_castSucc_eq ht weights (j := j)] using herase

/-- Helper for Remark 7.5: the cover-weight ordering also restricts to the old coordinates after
deleting an off-cover last variable. -/
private theorem remark_7_5_coverWeightsDescending_castSucc
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    (hdescending :
      remark_7_5_cover_weights_descending weights (Nat.le_trans ht (Nat.le_succ m))) :
    remark_7_5_cover_weights_descending
      (fun i : Fin m ↦ weights i.castSucc)
      ht := by
  intro i j hij
  simpa [remark_7_5_cover_weights_descending, remark_7_5_cover_weight] using hdescending hij

/-- Helper for Remark 7.5: the interval-index data on the shorter prefix stage is exactly the
restriction of the current stage to the old coordinates. -/
private theorem remark_7_5_intervalIndices_castSucc
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    (h : Fin (m + 1) → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h) :
    remark_7_5_interval_indices
      (fun i : Fin m ↦ weights i.castSucc)
      (remark_7_5_cover (n := m) t)
      (remark_7_5_mu (fun i : Fin m ↦ weights i.castSucc) t ht)
      (fun i : Fin m ↦ h i.castSucc) := by
  intro j hj
  have hj' : j.castSucc ∉ remark_7_5_cover (n := m + 1) t := by
    simpa [remark_7_5_cover_mem_iff] using hj
  simpa [remark_7_5_mu_castSucc_eq ht weights] using hinterval j.castSucc hj'

/-- Helper for Remark 7.5: the positive and capacity-bounded weight assumptions also restrict to
the shorter prefix stage. -/
private theorem remark_7_5_castSuccWeightBounds
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity) :
      (∀ j : Fin m, 0 < weights j.castSucc) ∧
      (∀ j : Fin m, weights j.castSucc ≤ capacity) := by
  exact ⟨fun j ↦ hweights_pos j.castSucc, fun j ↦ hweights_le j.castSucc⟩

/-- Helper for Remark 7.5: on the literal one slice `x_last = 1`, the old coordinates consume at
most the residual capacity left after paying for the last coordinate, hence also after paying for
the interval lower bound `μ_{h(last)}`. -/
private theorem remark_7_5_oneSliceResidualCapacity
    {m t : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (ht : t ≤ m)
    (h : Fin (m + 1) → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h) :
    ∀ x : Fin (m + 1) → ℝ,
      x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) →
        x (Fin.last m) = 1 →
          ∑ i : Fin m, (weights i.castSucc : ℝ) * x i.castSucc ≤
            (capacity : ℝ) -
              remark_7_5_mu
                weights
                t
                (Nat.le_trans ht (Nat.le_succ m))
                (h (Fin.last m)) := by
  intro x hx hxlast
  have hjLast : Fin.last m ∉ remark_7_5_cover (n := m + 1) t := by
    simp [remark_7_5_cover, Nat.not_lt.mpr ht]
  have hlast_mu_le_nat :
      remark_7_5_mu
          weights
          t
          (Nat.le_trans ht (Nat.le_succ m))
          (h (Fin.last m)) ≤
        weights (Fin.last m) := by
    exact (hinterval (Fin.last m) hjLast).1
  have hlast_mu_le :
      (remark_7_5_mu
          weights
          t
          (Nat.le_trans ht (Nat.le_succ m))
          (h (Fin.last m)) : ℝ) ≤
        weights (Fin.last m) := by
    exact_mod_cast hlast_mu_le_nat
  rw [mem_zero_one_knapsack_set_iff] at hx
  have hweight_split :
      ∑ i, (weights i : ℝ) * x i =
        ∑ i : Fin m, (weights i.castSucc : ℝ) * x i.castSucc +
          (weights (Fin.last m) : ℝ) * x (Fin.last m) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Fin.sum_univ_castSucc (f := fun i : Fin (m + 1) ↦ (weights i : ℝ) * x i))
  have hresidual_last :
      ∑ i : Fin m, (weights i.castSucc : ℝ) * x i.castSucc + weights (Fin.last m) ≤ capacity := by
    -- Splitting the knapsack weight once isolates the old-coordinate contribution.
    have hxcapacity := hx.2
    rw [hweight_split, hxlast] at hxcapacity
    simpa using hxcapacity
  -- Replacing the last-coordinate weight by the weaker lower bound `μ_{h(last)}` yields the
  -- residual-capacity inequality needed in the one-slice argument.
  linarith

/-- Helper for Remark 7.5: the zero-extended sequence of ordered cover weights remains
antitone on natural-number indices. -/
private theorem remark_7_5_extendedCoverWeight_antitone
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht) :
    Antitone (fun i : ℕ ↦ if hi : i < t then weights ⟨i, Nat.lt_of_lt_of_le hi ht⟩ else 0) := by
  intro i j hij
  by_cases hj : j < t
  · have hi : i < t := Nat.lt_of_le_of_lt hij hj
    have hordered := hdescending (show (⟨i, hi⟩ : Fin t) ≤ ⟨j, hj⟩ by exact hij)
    simpa [remark_7_5_cover_weights_descending, remark_7_5_cover_weight, hi, hj] using hordered
  · by_cases hi : i < t
    · simp [hi, hj]
    · simp [hi, hj]

/-- Helper for Remark 7.5: the ordered prefix sums are monotone in their length. -/
private theorem remark_7_5_mu_mono
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    {a b : ℕ}
    (hab : a ≤ b) :
    remark_7_5_mu weights t ht a ≤ remark_7_5_mu weights t ht b := by
  -- Extend the shorter range inside the longer one; every omitted summand is nonnegative.
  unfold remark_7_5_mu
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hab)
      (fun _ _ _ ↦ Nat.zero_le _)

/-- Helper for Remark 7.5: partial sums of descending cover weights are subadditive, including
after the sequence has stabilized at the cover length. -/
private theorem remark_7_5_mu_add_le_add_mu
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (a b : ℕ) :
    remark_7_5_mu weights t ht (a + b) ≤
      remark_7_5_mu weights t ht a + remark_7_5_mu weights t ht b := by
  let f : ℕ → ℕ :=
    fun i ↦ if hi : i < t then weights ⟨i, Nat.lt_of_lt_of_le hi ht⟩ else 0
  have hf : Antitone f := by
    simpa [f] using remark_7_5_extendedCoverWeight_antitone weights t ht hdescending
  have htail :
      (Finset.range b).sum (fun i ↦ f (a + i)) ≤ (Finset.range b).sum f := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hf (Nat.le_add_left i a)
  -- Split the longer prefix at `a`; antitonicity bounds the translated tail by the first `b` terms.
  simpa [remark_7_5_mu, f, Finset.sum_range_add] using
    Nat.add_le_add_left htail ((Finset.range a).sum f)

/-- Helper for Remark 7.5: the `i`-th element of a strictly increasing finite enumeration has
natural value at least `i`. -/
private theorem remark_7_5_fin_le_strictMono_val
    {q r : ℕ}
    (f : Fin q → Fin r)
    (hf : StrictMono f)
    (i : Fin q) :
    (i : ℕ) ≤ (f i : ℕ) := by
  have haux : ∀ k, ∀ hk : k < q, k ≤ (f ⟨k, hk⟩ : ℕ) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact Nat.zero_le _
    | succ k ih =>
        intro hk
        have hk' : k < q := Nat.lt_trans (Nat.lt_succ_self k) hk
        have hstep : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := by
          exact hf (by simp)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hk') hstep)
  exact haux i i.isLt

/-- Helper for Remark 7.5: among descending prefix weights, any selected cover subset weighs at
most the initial prefix having the same cardinality. -/
private theorem remark_7_5_coverSubset_sum_le_mu_card
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (S : Finset (Fin n))
    (hS : S ⊆ remark_7_5_cover t) :
    S.sum weights ≤ remark_7_5_mu weights t ht S.card := by
  classical
  have hcard : S.card ≤ t := by
    calc
      S.card ≤ (remark_7_5_cover (n := n) t).card := Finset.card_le_card hS
      _ = t := remark_7_5_cover_card t ht
  let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  have hterm :
      ∀ i : Fin S.card, weights (e i) ≤ weights (i.castLE (Nat.le_trans hcard ht)) := by
    intro i
    have heiMem : e i ∈ remark_7_5_cover (n := n) t :=
      hS (by simp [e])
    let ei : Fin t := ⟨(e i : ℕ), remark_7_5_cover_mem_iff.mp heiMem⟩
    have hie : i.castLE hcard ≤ ei := by
      rw [Fin.le_iff_val_le_val]
      exact remark_7_5_fin_le_strictMono_val e e.strictMono i
    have hweight := hdescending hie
    simpa [remark_7_5_cover_weights_descending, remark_7_5_cover_weight, e, ei] using hweight
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
    _ = remark_7_5_mu weights t ht S.card := by
      rw [remark_7_5_mu, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hit : (i : ℕ) < t := Nat.lt_of_lt_of_le i.isLt hcard
      rw [dif_pos hit]
      exact congrArg weights (Fin.ext rfl)

/-- Helper for Remark 7.5: a selected part of the cover pays for the terminal block of cover
weights having the same cardinality. -/
private theorem remark_7_5_mu_le_selectedCoverWeight_add
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (A : Finset (Fin n))
    (hA : A ⊆ remark_7_5_cover t) :
    remark_7_5_mu weights t ht t ≤
      A.sum weights + remark_7_5_mu weights t ht (t - A.card) := by
  let B := remark_7_5_cover (n := n) t \ A
  have hB : B ⊆ remark_7_5_cover (n := n) t := Finset.sdiff_subset
  have hcard : A.card ≤ t := by
    rw [← remark_7_5_cover_card t ht]
    exact Finset.card_le_card hA
  have hBcard : B.card = t - A.card := by
    rw [show B = remark_7_5_cover (n := n) t \ A by rfl, Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr hA, remark_7_5_cover_card t ht]
  have hBupper : B.sum weights ≤ remark_7_5_mu weights t ht (t - A.card) := by
    simpa [hBcard] using
      remark_7_5_coverSubset_sum_le_mu_card weights t ht hdescending B hB
  have hsplit : B.sum weights + A.sum weights = remark_7_5_mu weights t ht t := by
    calc
      B.sum weights + A.sum weights = (remark_7_5_cover (n := n) t).sum weights := by
        simpa [B] using Finset.sum_sdiff hA (f := weights)
      _ = remark_7_5_mu weights t ht t := remark_7_5_cover_sum_eq_mu weights t ht
  omega

/-- Helper for Remark 7.5: the interval lower bounds make the selected off-cover items pay for
the prefix sum indexed by their total lifting score. -/
private theorem remark_7_5_mu_selectedOutsideScore_le_weight
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (h : Fin n → ℕ)
    (hintervalLower :
      ∀ j, j ∉ remark_7_5_cover (n := n) t → remark_7_5_mu weights t ht (h j) ≤ weights j)
    (B : Finset (Fin n))
    (hB : ∀ j ∈ B, j ∉ remark_7_5_cover (n := n) t) :
    remark_7_5_mu weights t ht (B.sum h) ≤ B.sum weights := by
  classical
  induction B using Finset.induction_on with
  | empty =>
      simp [remark_7_5_mu]
  | @insert j B hj ih =>
      have hjOutside : j ∉ remark_7_5_cover (n := n) t := hB j (Finset.mem_insert_self j B)
      have hBOld : ∀ i ∈ B, i ∉ remark_7_5_cover (n := n) t := by
        intro i hi
        exact hB i (Finset.mem_insert_of_mem hi)
      have hsubadd :=
        remark_7_5_mu_add_le_add_mu weights t ht hdescending (B.sum h) (h j)
      calc
        remark_7_5_mu weights t ht ((insert j B).sum h)
            = remark_7_5_mu weights t ht (B.sum h + h j) := by
                simp [Finset.sum_insert, hj, add_comm]
        _ ≤ remark_7_5_mu weights t ht (B.sum h) + remark_7_5_mu weights t ht (h j) := hsubadd
        _ ≤ B.sum weights + weights j :=
          Nat.add_le_add (ih hBOld) (hintervalLower j hjOutside)
        _ = (insert j B).sum weights := by
          simp [Finset.sum_insert, hj, add_comm]

/-- Helper for Remark 7.5: enough selected lifting-score units, together with an initial prefix
of length `k`, carry at least the full cover weight. -/
private theorem remark_7_5_mu_le_selectedWeight_add
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (h : Fin n → ℕ)
    (hintervalLower :
      ∀ j, j ∉ remark_7_5_cover (n := n) t → remark_7_5_mu weights t ht (h j) ≤ weights j)
    (S : Finset (Fin n))
    (k : ℕ)
    (hscore :
      t ≤ k + ((S ∩ remark_7_5_cover t).card + (S \ remark_7_5_cover t).sum h)) :
    remark_7_5_mu weights t ht t ≤ S.sum weights + remark_7_5_mu weights t ht k := by
  let A := S ∩ remark_7_5_cover (n := n) t
  let B := S \ remark_7_5_cover (n := n) t
  have hA : A ⊆ remark_7_5_cover (n := n) t := Finset.inter_subset_right
  have hB : ∀ j ∈ B, j ∉ remark_7_5_cover (n := n) t := by
    intro j hj
    exact (Finset.mem_sdiff.mp hj).2
  have hcover := remark_7_5_mu_le_selectedCoverWeight_add weights t ht hdescending A hA
  have hoff :=
    remark_7_5_mu_selectedOutsideScore_le_weight
      weights t ht hdescending h hintervalLower B hB
  have hremaining : t - A.card ≤ B.sum h + k := by
    dsimp [A, B]
    omega
  have hmono := remark_7_5_mu_mono weights t ht hremaining
  have hsplit := remark_7_5_mu_add_le_add_mu weights t ht hdescending (B.sum h) k
  have htail :
      remark_7_5_mu weights t ht (t - A.card) ≤ B.sum weights + remark_7_5_mu weights t ht k := by
    calc
      remark_7_5_mu weights t ht (t - A.card)
          ≤ remark_7_5_mu weights t ht (B.sum h + k) := hmono
      _ ≤ remark_7_5_mu weights t ht (B.sum h) + remark_7_5_mu weights t ht k := hsplit
      _ ≤ B.sum weights + remark_7_5_mu weights t ht k := Nat.add_le_add_right hoff _
  have hpartition : A.sum weights + B.sum weights = S.sum weights := by
    have hdiff : S \ A = B := by
      ext i
      simp [A, B]
    calc
      A.sum weights + B.sum weights = (S \ A).sum weights + A.sum weights := by
        rw [hdiff]
        exact Nat.add_comm _ _
      _ = S.sum weights := Finset.sum_sdiff Finset.inter_subset_left
  omega

/-- Helper for Remark 7.5: an off-cover interval index is strictly below the cover length. -/
private theorem remark_7_5_intervalIndex_succ_le
    (weights : Fin n → ℕ)
    (t : ℕ)
    (ht : t ≤ n)
    (h : Fin n → ℕ)
    (hinterval :
      remark_7_5_interval_indices weights (remark_7_5_cover (n := n) t)
        (remark_7_5_mu weights t ht) h)
    {j : Fin n}
    (hj : j ∉ remark_7_5_cover (n := n) t) :
    h j + 1 ≤ t := by
  by_contra hnot
  have ht_le_hj : t ≤ h j := by omega
  have ht_le_hjSucc : t ≤ h j + 1 := by omega
  have hμj := remark_7_5_mu_eq_of_ge weights t ht (h j) ht_le_hj
  have hμjSucc := remark_7_5_mu_eq_of_ge weights t ht (h j + 1) ht_le_hjSucc
  have hjInterval := hinterval j hj
  rw [hμj, hμjSucc] at hjInterval
  omega

/-- Helper for Remark 7.5: on the one slice of the successor prefix stage, feasibility should
bound the old partial lifting value by the remaining cover slack. -/
private theorem remark_7_5_stageOneSliceUpperBound
    {m t : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (ht : t ≤ m)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := m + 1) t))
    (hdescending :
      remark_7_5_cover_weights_descending weights (Nat.le_trans ht (Nat.le_succ m)))
    (h : Fin (m + 1) → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h) :
    ∀ x : Fin (m + 1) → ℝ,
      x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) →
        x (Fin.last m) = 1 →
          partial_lifting_value
              (remark_7_5_lifting_coeff
                (remark_7_5_cover (n := m) t)
                (fun i : Fin m ↦ h i.castSucc))
              x ≤
            cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) - h (Fin.last m) := by
  classical
  intro x hx hxlast
  have hresidual :=
    remark_7_5_oneSliceResidualCapacity
      weights
      capacity
      ht
      h
      hinterval
      x
      hx
      hxlast
  let oldWeights : Fin m → ℕ := fun i ↦ weights i.castSucc
  let oldIndices : Fin m → ℕ := fun i ↦ h i.castSucc
  let oldCover : Finset (Fin m) := remark_7_5_cover t
  let selected : Finset (Fin m) := Finset.univ.filter fun i ↦ x i.castSucc = 1
  let score : ℕ :=
    (selected ∩ oldCover).card + (selected \ oldCover).sum oldIndices
  have hxBinary : ∀ i : Fin m, x i.castSucc = 0 ∨ x i.castSucc = 1 := by
    have hx' := hx
    rw [mem_zero_one_knapsack_set_iff] at hx'
    intro i
    exact hx'.1 i.castSucc
  have hxOne : ∀ {i : Fin m}, i ∈ selected → x i.castSucc = 1 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hxZero : ∀ {i : Fin m}, i ∉ selected → x i.castSucc = 0 := by
    intro i hi
    rcases hxBinary i with hiZero | hiOne
    · exact hiZero
    · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiOne⟩))
  have hcoverPart :
      oldCover.sum (fun i ↦ x i.castSucc) = ((selected ∩ oldCover).card : ℝ) := by
    calc
      oldCover.sum (fun i ↦ x i.castSucc) =
          oldCover.sum (fun i ↦ if i ∈ selected then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hiSelected : i ∈ selected
            · simp [hiSelected, hxOne hiSelected]
            · simp [hiSelected, hxZero hiSelected]
      _ = ((oldCover ∩ selected).card : ℝ) := by
            simp
      _ = ((selected ∩ oldCover).card : ℝ) := by
            rw [Finset.inter_comm]
  have hoffCoverPart :
      (Finset.univ \ oldCover).sum
          (fun i ↦ (oldIndices i : ℝ) * x i.castSucc) =
        (((selected \ oldCover).sum oldIndices : ℕ) : ℝ) := by
    calc
      (Finset.univ \ oldCover).sum (fun i ↦ (oldIndices i : ℝ) * x i.castSucc) =
          (Finset.univ \ oldCover).sum
            (fun i ↦ if i ∈ selected then (oldIndices i : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hiSelected : i ∈ selected
              · simp [hiSelected, hxOne hiSelected]
              · simp [hiSelected, hxZero hiSelected]
      _ = ((selected \ oldCover).sum fun i ↦ (oldIndices i : ℝ)) := by
            rw [← Finset.sum_filter]
            congr 1
            ext i
            simp [and_comm]
      _ = (((selected \ oldCover).sum oldIndices : ℕ) : ℝ) := by
            rw [Nat.cast_sum]
  have hpartial :
      partial_lifting_value
          (remark_7_5_lifting_coeff oldCover oldIndices)
          x = (score : ℝ) := by
    have hsplit :=
      remark_7_5_lifting_coeff_dotProduct
        oldCover oldIndices (fun i : Fin m ↦ x i.castSucc)
    rw [partial_lifting_value_eq_sum]
    change
      remark_7_5_lifting_coeff oldCover oldIndices ⬝ᵥ (fun i : Fin m ↦ x i.castSucc) =
        (score : ℝ)
    rw [hsplit, hcoverPart, hoffCoverPart]
    simp [score]
  have hweightSelected :
      ∑ i : Fin m, (oldWeights i : ℝ) * x i.castSucc =
        ((selected.sum oldWeights : ℕ) : ℝ) := by
    calc
      ∑ i : Fin m, (oldWeights i : ℝ) * x i.castSucc =
          ∑ i : Fin m, if i ∈ selected then (oldWeights i : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hiSelected : i ∈ selected
            · simp [hiSelected, hxOne hiSelected]
            · simp [hiSelected, hxZero hiSelected]
      _ = selected.sum (fun i ↦ (oldWeights i : ℝ)) := by
            simp only [selected, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ,
              true_and]
      _ = ((selected.sum oldWeights : ℕ) : ℝ) := by
            norm_cast
  have hlastOutside : Fin.last m ∉ remark_7_5_cover (n := m + 1) t := by
    simp [remark_7_5_cover_mem_iff, Nat.not_lt.mpr ht]
  have hlastIndex : h (Fin.last m) + 1 ≤ t :=
    remark_7_5_intervalIndex_succ_le
      weights t (Nat.le_trans ht (Nat.le_succ m)) h hinterval hlastOutside
  have htargetNat : score ≤ t - 1 - h (Fin.last m) := by
    by_contra hnot
    have hscoreThreshold : t ≤ h (Fin.last m) + score := by
      omega
    have hdescendingOld := remark_7_5_coverWeightsDescending_castSucc ht weights hdescending
    have hintervalOld := remark_7_5_intervalIndices_castSucc ht weights h hinterval
    have hmajor :
        remark_7_5_mu oldWeights t ht t ≤
          selected.sum oldWeights + remark_7_5_mu oldWeights t ht (h (Fin.last m)) := by
      exact
        remark_7_5_mu_le_selectedWeight_add
          oldWeights
          t
          ht
          hdescendingOld
          oldIndices
          (fun j hj ↦ (hintervalOld j hj).1)
          selected
          (h (Fin.last m))
          (by simpa [score, add_comm, add_left_comm, add_assoc] using hscoreThreshold)
    have hselectedWithPrefixLe :
        selected.sum oldWeights + remark_7_5_mu oldWeights t ht (h (Fin.last m)) ≤ capacity := by
      have hreal :
          ((selected.sum oldWeights + remark_7_5_mu oldWeights t ht (h (Fin.last m)) : ℕ) : ℝ) ≤
            capacity := by
        rw [Nat.cast_add, ← hweightSelected]
        rw [remark_7_5_mu_castSucc_eq ht weights]
        dsimp [oldWeights]
        linarith
      exact_mod_cast hreal
    have hcapacityLt :
        capacity < remark_7_5_mu oldWeights t ht t := by
      have hcover :
          IsKnapsackCover oldWeights capacity (remark_7_5_cover (n := m) t) :=
        (remark_7_5_minimalCover_castSucc capacity ht weights hCmin).toIsKnapsackCover
      have hcoverLt :=
        (isKnapsackCover_iff oldWeights capacity (remark_7_5_cover (n := m) t)).mp hcover
      simpa [remark_7_5_cover_sum_eq_mu oldWeights t ht] using hcoverLt
    omega
  have htargetReal :
      (score : ℝ) ≤ (t : ℝ) - 1 - h (Fin.last m) := by
    have hlastLe : h (Fin.last m) ≤ t - 1 := by omega
    calc
      (score : ℝ) ≤ ((t - 1 - h (Fin.last m) : ℕ) : ℝ) := by exact_mod_cast htargetNat
      _ = (t : ℝ) - 1 - h (Fin.last m) := by
        rw [Nat.cast_sub hlastLe, Nat.cast_sub (by omega : 1 ≤ t)]
        norm_num
  have hpartial' :
      partial_lifting_value
          (remark_7_5_lifting_coeff
            (remark_7_5_cover (n := m) t)
            (fun i : Fin m ↦ h i.castSucc))
          x = (score : ℝ) := by
    simpa [oldCover, oldIndices] using hpartial
  rw [hpartial', cover_inequality_rhs_eq,
    remark_7_5_cover_card (n := m + 1) t (Nat.le_trans ht (Nat.le_succ m))]
  exact htargetReal

/-- Helper for Remark 7.5: the interval-index coefficients should yield a valid lifted cover
inequality on the binary knapsack set before passing to the polytope owner. -/
private theorem remark_7_5_setValidOfIntervalIndicesNormalized
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := n) t))
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (h : Fin n → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := n) t)
        (remark_7_5_mu weights t ht)
        h) :
    is_valid_inequality
      (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h)
      (cover_inequality_rhs (remark_7_5_cover (n := n) t)) := by
  rcases Nat.exists_eq_add_of_le ht with ⟨m, rfl⟩
  -- Route correction: stay in the literal-last-coordinate prefix model and induct on the number
  -- of off-cover coordinates.
  let go :
      ∀ m : ℕ,
        ∀ weights : Fin (t + m) → ℕ,
          remark_7_5_cover_weights_descending weights (Nat.le_add_right t m) →
          (∀ j, 0 < weights j) →
          (∀ j, weights j ≤ capacity) →
          IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := t + m) t) →
          ∀ h : Fin (t + m) → ℕ,
            remark_7_5_interval_indices
              weights
              (remark_7_5_cover (n := t + m) t)
              (remark_7_5_mu weights t (Nat.le_add_right t m))
              h →
              is_valid_inequality
                (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
                (remark_7_5_lifting_coeff (remark_7_5_cover (n := t + m) t) h)
                (cover_inequality_rhs (remark_7_5_cover (n := t + m) t)) := by
    intro m
    induction m with
    | zero =>
        -- In the base stage the cover is the whole index set, so the remark coefficients reduce
        -- to the original cover inequality.
        intro weights hdescending hweights_pos hweights_le hCmin h hinterval x hx
        have hxpoly :
            x ∈ zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ) := by
          rw [zero_one_knapsack_polytope_eq_convexHull]
          exact subset_convexHull ℝ _ hx
        have hvalid_poly :
            is_valid_inequality
              (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
              (cover_indicator (remark_7_5_cover (n := t) t))
              (cover_inequality_rhs (remark_7_5_cover (n := t) t)) := by
          exact
            coverInequality_validOnKnapsackPolytope
              weights
              capacity
              (remark_7_5_cover (n := t) t)
              hCmin.toIsKnapsackCover
        have hcoeff_eq :
            remark_7_5_lifting_coeff (remark_7_5_cover (n := t) t) h =
              cover_indicator (remark_7_5_cover (n := t) t) := by
          have huniv : remark_7_5_cover (n := t) t = Finset.univ := by
            ext i
            simp [remark_7_5_cover_mem_iff]
          simpa [huniv] using remark_7_5_univCoverCoeff_eq_coverIndicator h
        simpa [hcoeff_eq] using hvalid_poly hxpoly
    | succ m ih =>
        intro weights hdescending hweights_pos hweights_le hCmin h hinterval
        let αPrev : Fin (t + m) → ℝ :=
          remark_7_5_lifting_coeff
            (remark_7_5_cover (n := t + m) t)
            (fun i : Fin (t + m) ↦ h i.castSucc)
        have hcastBounds :=
          remark_7_5_castSuccWeightBounds weights capacity hweights_pos hweights_le
        have hvalidPrev :
            is_valid_inequality
              (zero_one_knapsack_set
                (fun j : Fin (t + m) ↦ (weights j.castSucc : ℝ))
                (capacity : ℝ))
              αPrev
              (cover_inequality_rhs (remark_7_5_cover (n := t + m) t)) := by
          -- Restrict the theorem to the old coordinates and apply the induction hypothesis there.
          exact
            ih
              (fun j : Fin (t + m) ↦ weights j.castSucc)
              (remark_7_5_coverWeightsDescending_castSucc
                (Nat.le_add_right t m)
                weights
                hdescending)
              hcastBounds.1
              hcastBounds.2
              (remark_7_5_minimalCover_castSucc
                capacity
                (Nat.le_add_right t m)
                weights
                hCmin)
              (fun j : Fin (t + m) ↦ h j.castSucc)
              (remark_7_5_intervalIndices_castSucc
                (Nat.le_add_right t m)
                weights
                h
                hinterval)
        have hbeta_eq :
            cover_inequality_rhs (remark_7_5_cover (n := t + m) t) =
              cover_inequality_rhs (remark_7_5_cover (n := t + m + 1) t) := by
          rw [cover_inequality_rhs_eq, cover_inequality_rhs_eq,
            remark_7_5_cover_card (n := t + m) t (Nat.le_add_right t m),
            remark_7_5_cover_card (n := t + m + 1) t
              (Nat.le_trans (Nat.le_add_right t m) (Nat.le_succ _))]
        have hzero :
            is_valid_inequality
              (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ) ∩
                last_coordinate_eq_set (t + m) 0)
              (Fin.snoc αPrev 0)
              (cover_inequality_rhs (remark_7_5_cover (n := t + m + 1) t)) := by
          -- The zero slice is exactly the previous-stage problem with one appended zero coordinate.
          exact
            remark_7_5_lastCoordinateZeroSliceValid
              weights
              capacity
              αPrev
              (cover_inequality_rhs (remark_7_5_cover (n := t + m + 1) t))
              (by simpa [hbeta_eq] using hvalidPrev)
        have hone :=
          remark_7_5_stageOneSliceUpperBound
            weights
            capacity
            (Nat.le_add_right t m)
            hCmin
            hdescending
            h
            hinterval
        have hsnoc :
            remark_7_5_lifting_coeff (remark_7_5_cover (n := t + m + 1) t) h =
              Fin.snoc αPrev (h (Fin.last (t + m))) :=
          remark_7_5_liftingCoeff_snoc (Nat.le_add_right t m) h
        have hvalidSucc :
            is_valid_inequality
              (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
              (Fin.snoc αPrev (h (Fin.last (t + m))))
              (cover_inequality_rhs (remark_7_5_cover (n := t + m + 1) t)) :=
          remark_7_5_valid_of_zeroSlice_and_oneSliceBound
            weights
            capacity
            αPrev
            (cover_inequality_rhs (remark_7_5_cover (n := t + m + 1) t))
            (h (Fin.last (t + m)))
            hzero
            hone
        -- Once the zero and one slices are handled, the whole successor stage follows.
        exact hsnoc ▸ hvalidSucc
  exact go m weights hdescending hweights_pos hweights_le hCmin h hinterval

/-- Helper for Remark 7.5: the interval-index coefficients should yield a valid lifted cover
inequality on the binary knapsack set before passing to the polytope owner. -/
private theorem remark_7_5_setValidOfIntervalIndices
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (hctx : ∃ lam, remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h) :
    is_valid_inequality
      (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff C h)
      (cover_inequality_rhs C) := by
  rcases hctx with ⟨lam, t, ht, rfl, hdescending, hweights_pos, hweights_le, hCmin, rfl, hlam⟩
  -- Route correction: validity is now reduced to the normalized prefix-stage induction above.
  exact
    remark_7_5_setValidOfIntervalIndicesNormalized
      weights
      capacity
      t
      ht
      hweights_pos
      hweights_le
      hCmin
      hdescending
      h
      hinterval

/-- Helper for Remark 7.5: the strengthened upper-bound hypothesis also restricts to the old
coordinates after deleting an off-cover last variable. -/
private theorem remark_7_5_strongUpperBound_castSucc
    {m t : ℕ}
    (ht : t ≤ m)
    (weights : Fin (m + 1) → ℕ)
    (h : Fin (m + 1) → ℕ)
    (lam : ℕ)
    (hupper :
      remark_7_5_strong_upper_bound
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h
        lam) :
    remark_7_5_strong_upper_bound
      (fun i : Fin m ↦ weights i.castSucc)
      (remark_7_5_cover (n := m) t)
      (remark_7_5_mu (fun i : Fin m ↦ weights i.castSucc) t ht)
      (fun i : Fin m ↦ h i.castSucc)
      lam := by
  intro j hj
  have hj' : j.castSucc ∉ remark_7_5_cover (n := m + 1) t := by
    simpa [remark_7_5_cover_mem_iff] using hj
  simpa [remark_7_5_mu_castSucc_eq ht weights] using hupper j.castSucc hj'

/-- Helper for Remark 7.5: the strengthened upper bound produces a feasible one-slice witness at
the literal last coordinate that is tight for the canonical coefficient `h (Fin.last m)`. -/
private theorem remark_7_5_lastCoordinateTightWitness
    {m t : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (ht : t ≤ m)
    (hweights_pos : ∀ j, 0 < weights j)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := m + 1) t))
    (h : Fin (m + 1) → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h)
    (lam : ℕ)
    (hlam :
      lam =
        remark_7_5_cover_excess
          weights
          capacity
          t
          (Nat.le_trans ht (Nat.le_succ m)))
    (hupper :
      remark_7_5_strong_upper_bound
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h
        lam) :
    ∃ x : Fin (m + 1) → ℝ,
      x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∧
        x (Fin.last m) = 1 ∧
          partial_lifting_value
              (remark_7_5_lifting_coeff
                (remark_7_5_cover (n := m) t)
                (fun i : Fin m ↦ h i.castSucc))
              x =
            cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) - h (Fin.last m) := by
  have hjLast : Fin.last m ∉ remark_7_5_cover (n := m + 1) t := by
    simp [remark_7_5_cover_mem_iff, Nat.not_lt.mpr ht]
  have hs : h (Fin.last m) + 1 ≤ t := by
    -- The interval condition forces the last off-cover index to occur before the cover sum
    -- stabilizes.
    by_contra hs
    have ht_le_hlast : t ≤ h (Fin.last m) := by
      omega
    have ht_le_hlast_succ : t ≤ h (Fin.last m) + 1 := by
      omega
    have hμlast :
        remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m)) =
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t :=
      remark_7_5_mu_eq_of_ge
        weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m)) ht_le_hlast
    have hμlastSucc :
        remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) =
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t :=
      remark_7_5_mu_eq_of_ge
        weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) ht_le_hlast_succ
    have hlastInterval := hinterval (Fin.last m) hjLast
    rw [hμlast, hμlastSucc] at hlastInterval
    omega
  let x : Fin (m + 1) → ℝ := remark_7_5_suffixWitness t (Fin.last m) (h (Fin.last m) + 1)
  have hupperLast :
      weights (Fin.last m) ≤
        remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) -
          remark_7_5_cover_excess weights capacity t (Nat.le_trans ht (Nat.le_succ m)) :=
    by simpa [hlam] using hupper (Fin.last m) hjLast
  have hweight_nat :
      weights (Fin.last m) +
          (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t -
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1)) ≤
        capacity := by
    -- Normalize the strengthened upper bound to the feasibility inequality used by the suffix
    -- witness.
    have hposLast : 0 < weights (Fin.last m) := hweights_pos (Fin.last m)
    have hcoverExcess_lt :
        remark_7_5_cover_excess weights capacity t (Nat.le_trans ht (Nat.le_succ m)) <
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) := by
      exact
        (Nat.sub_pos_iff_lt.mp <|
          lt_of_lt_of_le hposLast (by simpa [hlam] using hupperLast))
    have hupperLast_add :
        weights (Fin.last m) +
            remark_7_5_cover_excess weights capacity t (Nat.le_trans ht (Nat.le_succ m)) ≤
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) := by
      exact
        (Nat.le_sub_iff_add_le hcoverExcess_lt.le).mp (by simpa [hlam] using hupperLast)
    have hmu_prefix_le :
        remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) ≤
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t := by
      have hs_le_n : h (Fin.last m) + 1 ≤ m + 1 := Nat.le_trans hs (Nat.le_trans ht (Nat.le_succ m))
      have hprefix_sum_le :
          (remark_7_5_cover (n := m + 1) (h (Fin.last m) + 1)).sum weights ≤
            (remark_7_5_cover (n := m + 1) t).sum weights :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (remark_7_5_cover_subset (n := m + 1) hs)
          (by
            intro i hi hino
            exact Nat.zero_le _)
      have hprefix_sum_eq :
          (remark_7_5_cover (n := m + 1) (h (Fin.last m) + 1)).sum weights =
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) := by
        calc
          (remark_7_5_cover (n := m + 1) (h (Fin.last m) + 1)).sum weights
              = remark_7_5_mu weights (h (Fin.last m) + 1) hs_le_n (h (Fin.last m) + 1) := by
                  rw [remark_7_5_cover_sum_eq_mu]
          _ = remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) := by
                rw [remark_7_5_mu_prefix_eq weights hs_le_n (Nat.le_trans ht (Nat.le_succ m)) hs]
      have hcover_sum_eq :
          (remark_7_5_cover (n := m + 1) t).sum weights =
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t := by
        rw [remark_7_5_cover_sum_eq_mu]
      rw [hprefix_sum_eq, hcover_sum_eq] at hprefix_sum_le
      exact hprefix_sum_le
    simp only [ge_iff_le] at hupperLast_add ⊢
    have hmu_t_ge_capacity :
        capacity ≤ remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t := by
      have hcover : IsKnapsackCover weights capacity (remark_7_5_cover (n := m + 1) t) :=
        inferInstance
      have hcover_lt :
          capacity < (remark_7_5_cover (n := m + 1) t).sum weights :=
        (isKnapsackCover_iff weights capacity (remark_7_5_cover (n := m + 1) t)).mp hcover
      rw [remark_7_5_cover_sum_eq_mu weights t (Nat.le_trans ht (Nat.le_succ m))] at hcover_lt
      exact Nat.le_of_lt hcover_lt
    have hupperLast_total :
        weights (Fin.last m) +
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t ≤
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) +
            capacity := by
      have hupperLast_add_capacity := Nat.add_le_add_right hupperLast_add capacity
      calc
        weights (Fin.last m) +
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t
            = weights (Fin.last m) +
                ((remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t - capacity) +
                  capacity) := by
                    rw [Nat.sub_add_cancel hmu_t_ge_capacity]
        _ =
            (weights (Fin.last m) +
                (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t - capacity)) +
              capacity := by
                omega
        _ ≤
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) +
              capacity := hupperLast_add_capacity
    have hmu_split :
        remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t =
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) +
            (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t -
              remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1)) := by
      omega
    have hcombined :
        weights (Fin.last m) +
            (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t -
              remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1)) +
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) ≤
          remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) +
            capacity := by
      calc
        weights (Fin.last m) +
            (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t -
              remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1)) +
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1)
            = weights (Fin.last m) +
                remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) t := by
                  rw [hmu_split]
                  omega
        _ ≤
            remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)) (h (Fin.last m) + 1) +
              capacity := hupperLast_total
    omega
  have hx_set :
      x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
    -- The explicit suffix witness is feasible exactly under the normalized residual inequality.
    refine
      remark_7_5_suffixWitnessFeasible
        weights
        capacity
        t
        (Nat.le_trans ht (Nat.le_succ m))
        hjLast
        (h (Fin.last m) + 1)
        hs
        ?_
    exact_mod_cast hweight_nat
  have hx_last : x (Fin.last m) = 1 := by
    -- The suffix witness always turns on the designated last coordinate.
    simp [x, remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport]
  let αPrev : Fin m → ℝ :=
    remark_7_5_lifting_coeff
      (remark_7_5_cover (n := m) t)
      (fun i : Fin m ↦ h i.castSucc)
  have hx_eq :
      remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h ⬝ᵥ x =
        cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) := by
    -- The same suffix witness saturates the canonical lifted inequality at equality.
    calc
      remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h ⬝ᵥ x
          =
            remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h ⬝ᵥ
              remark_7_5_suffixWitness t (Fin.last m) (h (Fin.last m) + 1) := by
                rfl
      _ = remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h (Fin.last m) +
            ((t - (h (Fin.last m) + 1 : ℕ)) : ℝ) := by
              refine
                remark_7_5_suffixWitnessCoeff
                  (t := t)
                  (ht := Nat.le_trans ht (Nat.le_succ m))
                  (α := remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h)
                  ?_
                  hjLast
                  (h (Fin.last m) + 1)
                  hs
              intro i hi
              simpa using
                remark_7_5_lifting_coeff_apply_of_mem
                  (C := remark_7_5_cover (n := m + 1) t)
                  (h := h)
                  hi
      _ = (h (Fin.last m) : ℝ) + ((t - (h (Fin.last m) + 1 : ℕ)) : ℝ) := by
            simp [remark_7_5_lifting_coeff_apply_of_not_mem hjLast]
      _ = cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) := by
            rw [cover_inequality_rhs_eq,
              remark_7_5_cover_card (n := m + 1) t (Nat.le_trans ht (Nat.le_succ m))]
            norm_num
            ring
  have hx_partial :
      partial_lifting_value αPrev x =
        cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) - h (Fin.last m) := by
    have hx_snoc :
        Fin.snoc αPrev (h (Fin.last m)) ⬝ᵥ x =
          cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) := by
      simpa [αPrev, remark_7_5_liftingCoeff_snoc ht h] using hx_eq
    have hx_expand :
        partial_lifting_value αPrev x + (h (Fin.last m) : ℝ) * x (Fin.last m) =
          cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) := by
      simpa [dotProduct_last_coordinate_lifting_coeffs] using hx_snoc
    rw [hx_last] at hx_expand
    linarith
  exact ⟨x, hx_set, hx_last, hx_partial⟩

/-- Helper for Remark 7.5: in the strengthened branch, the literal last-coordinate coefficient
produced by Proposition 7.2 should agree with the canonical Remark 7.5 value. -/
private theorem remark_7_5_stageLastCoefficientEq
    {m t : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (ht : t ≤ m)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := m + 1) t))
    (hdescending :
      remark_7_5_cover_weights_descending weights (Nat.le_trans ht (Nat.le_succ m)))
    (h : Fin (m + 1) → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h)
    (lam : ℕ)
    (hlam :
      lam =
        remark_7_5_cover_excess
          weights
          capacity
          t
          (Nat.le_trans ht (Nat.le_succ m)))
    (hupper :
      remark_7_5_strong_upper_bound
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h
        lam) :
    last_coordinate_lifting_coefficient
      (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff
        (remark_7_5_cover (n := m) t)
        (fun i : Fin m ↦ h i.castSucc))
      (cover_inequality_rhs (remark_7_5_cover (n := m + 1) t)) =
      h (Fin.last m) := by
  let S := zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ)
  let αPrev : Fin m → ℝ :=
    remark_7_5_lifting_coeff
      (remark_7_5_cover (n := m) t)
      (fun i : Fin m ↦ h i.castSucc)
  let β := cover_inequality_rhs (remark_7_5_cover (n := m + 1) t)
  let coeff :=
    last_coordinate_lifting_coefficient
      S
      αPrev
      β
  have hcastBounds :=
    remark_7_5_castSuccWeightBounds weights capacity hweights_pos hweights_le
  have hvalidPrev :
      is_valid_inequality
        (zero_one_knapsack_set
          (fun j : Fin m ↦ (weights j.castSucc : ℝ))
          (capacity : ℝ))
        αPrev
        (cover_inequality_rhs (remark_7_5_cover (n := m) t)) := by
    -- Rebuild the old-stage validity before lifting the literal last coordinate.
    exact
      remark_7_5_setValidOfIntervalIndicesNormalized
        (fun j : Fin m ↦ weights j.castSucc)
        capacity
        t
        ht
        hcastBounds.1
        hcastBounds.2
        (remark_7_5_minimalCover_castSucc capacity ht weights hCmin)
        (remark_7_5_coverWeightsDescending_castSucc ht weights hdescending)
        (fun j : Fin m ↦ h j.castSucc)
        (remark_7_5_intervalIndices_castSucc ht weights h hinterval)
  have hbeta_eq :
      cover_inequality_rhs (remark_7_5_cover (n := m) t) =
        cover_inequality_rhs (remark_7_5_cover (n := m + 1) t) := by
    rw [cover_inequality_rhs_eq, cover_inequality_rhs_eq,
      remark_7_5_cover_card (n := m) t ht,
      remark_7_5_cover_card (n := m + 1) t (Nat.le_trans ht (Nat.le_succ _))]
  have hzero :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set m 0)
        (Fin.snoc αPrev 0)
        β := by
    -- The zero slice is the previous prefix stage with one appended zero coordinate.
    exact
      remark_7_5_lastCoordinateZeroSliceValid
        weights
        capacity
        αPrev
        β
        (by simpa [S, αPrev, β, hbeta_eq] using hvalidPrev)
  have hvalidCanonical :
      is_valid_inequality
        S
        (Fin.snoc αPrev (h (Fin.last m)))
        β := by
    -- Reuse the already-established stage-validity theorem on the current prefix problem.
    have hvalidCurrent :
        is_valid_inequality
          (zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
          (remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h)
          (cover_inequality_rhs (remark_7_5_cover (n := m + 1) t)) := by
      exact
        remark_7_5_setValidOfIntervalIndicesNormalized
          weights
          capacity
          t
          (Nat.le_trans ht (Nat.le_succ m))
          hweights_pos
          hweights_le
          hCmin
          hdescending
          h
          hinterval
    simpa [S, αPrev, β, remark_7_5_liftingCoeff_snoc ht h] using hvalidCurrent
  have hS_binary :
      S ⊆ zero_one_points (Nat.le_refl (m + 1)) (Set.univ : Set (Fin (m + 1) → ℝ)) := by
    simpa [S] using
      remark_7_5_zeroOneKnapsackSet_subset_zeroOnePointsUniv
        weights
        capacity
  have honeSliceNonempty : Set.Nonempty (S ∩ last_coordinate_eq_set m 1) := by
    -- The singleton last-coordinate point certifies that the `x_last = 1` slice is nonempty.
    refine ⟨Pi.single (Fin.last m) (1 : ℝ), ?_⟩
    refine ⟨?_, mem_last_coordinate_eq_set_iff.mpr (by simp)⟩
    exact remark_7_5_lastSingletonFeasible weights capacity hweights_le
  have hlast_le_coeff : (h (Fin.last m) : ℝ) ≤ coeff := by
    -- Proposition 7.2 bounds every valid last-coordinate coefficient by the maximal one.
    exact
      binary_last_coordinate_lifting_upper_bound
        S
        αPrev
        β
        hS_binary
        hzero
        honeSliceNonempty
        hvalidCanonical
  have hcoeffValid :
      is_valid_inequality
        S
        (Fin.snoc αPrev coeff)
        β := by
    -- The canonical Proposition 7.2 coefficient is valid by construction.
    exact
      binary_last_coordinate_lifting_is_valid
        S
        αPrev
        β
        hS_binary
        hzero
        honeSliceNonempty
  rcases
      remark_7_5_lastCoordinateTightWitness
        weights
        capacity
        ht
        hweights_pos
        hCmin
        h
        hinterval
        lam
        hlam
        hupper with
    ⟨x, hxS, hxlast, hxpartial⟩
  have hcoeff_le_last : coeff ≤ h (Fin.last m) := by
    -- Evaluating the maximal coefficient on a point tight for the canonical coefficient forces the
    -- reverse inequality.
    have hx_valid :
        partial_lifting_value αPrev x + coeff ≤ β := by
      simpa [S, αPrev, β, coeff, dotProduct_last_coordinate_lifting_coeffs, hxlast] using
        hcoeffValid hxS
    linarith
  exact le_antisymm hcoeff_le_last hlast_le_coeff

/-- Helper for Remark 7.5: appending a zero coordinate preserves addition. -/
private theorem remark_7_5_snocZero_add
    {m : ℕ}
    (x y : Fin m → ℝ) :
    (Fin.snoc (x + y) (0 : ℝ) : Fin (m + 1) → ℝ) =
      (Fin.snoc x (0 : ℝ) : Fin (m + 1) → ℝ) +
        (Fin.snoc y (0 : ℝ) : Fin (m + 1) → ℝ) := by
  -- Check the identity separately on the inherited coordinates and the appended coordinate.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp

/-- Helper for Remark 7.5: appending a zero coordinate preserves real scalar multiplication. -/
private theorem remark_7_5_snocZero_smul
    {m : ℕ}
    (a : ℝ)
    (x : Fin m → ℝ) :
    (Fin.snoc (a • x) (0 : ℝ) : Fin (m + 1) → ℝ) =
      a • (Fin.snoc x (0 : ℝ) : Fin (m + 1) → ℝ) := by
  -- Check the identity separately on the inherited coordinates and the appended coordinate.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp

/-- Helper for Remark 7.5: the canonical embedding into the last-coordinate zero hyperplane is
linear. -/
private def remark_7_5_snocZeroLinear (m : ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun := fun x ↦ Fin.snoc x 0
  map_add' := remark_7_5_snocZero_add
  map_smul' := remark_7_5_snocZero_smul

/-- Helper for Remark 7.5: the zero-coordinate embedding evaluates as `Fin.snoc x 0`. -/
@[simp] private theorem remark_7_5_snocZeroLinear_apply
    {m : ℕ}
    (x : Fin m → ℝ) :
    remark_7_5_snocZeroLinear m x = Fin.snoc x 0 := by
  -- The application rule is the defining data of the linear embedding.
  rfl

/-- Helper for Remark 7.5: the zero-coordinate embedding is injective. -/
private theorem remark_7_5_snocZeroLinear_injective
    {m : ℕ} :
    Function.Injective (remark_7_5_snocZeroLinear m) := by
  intro x y hxy
  -- Equality after appending zero can be read back on every inherited coordinate.
  funext i
  have hcoord := congrFun hxy i.castSucc
  simpa using hcoord

/-- Helper for Remark 7.5: a tight point of the previous-stage face remains tight after appending
a zero coordinate in the current zero slice. -/
private theorem remark_7_5_snocZero_mem_zeroSliceFace
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (alpha : Fin m → ℝ)
    (beta : ℝ)
    {y : Fin m → ℝ}
    (hy :
      y ∈
        face_set
          (zero_one_knapsack_polytope
            (fun i : Fin m ↦ (weights i.castSucc : ℝ))
            (capacity : ℝ))
          alpha
          beta) :
    Fin.snoc y 0 ∈
      face_set
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
          last_coordinate_eq_set m 0)
        (Fin.snoc alpha 0)
        beta := by
  let oldSet :=
    zero_one_knapsack_set
      (fun i : Fin m ↦ (weights i.castSucc : ℝ))
      (capacity : ℝ)
  let currentSet :=
    zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let L := remark_7_5_snocZeroLinear m
  have hsetImage : L '' oldSet ⊆ currentSet := by
    rintro z ⟨x, hx, rfl⟩
    rw [mem_zero_one_knapsack_set_iff] at hx ⊢
    constructor
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa [L] using hx.1 j
      · simp [L]
    · -- The appended coordinate contributes zero to the current knapsack weight.
      simpa [L, Fin.sum_univ_castSucc] using hx.2
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
  · -- Appending zero leaves the old exposing dot product unchanged.
    simpa [dotProduct_last_coordinate_lifting_coeffs, partial_lifting_value, dotProduct,
      Fin.sum_univ_castSucc] using hyData.2

/-- Helper for Remark 7.5: embedding the previous equality face in the current zero slice cannot
decrease the affine-span direction dimension. -/
private theorem remark_7_5_oldFace_finrank_le_zeroSliceFace
    {m : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (alpha : Fin m → ℝ)
    (beta : ℝ) :
    Module.finrank ℝ
        (affineSpan ℝ
          (face_set
            (zero_one_knapsack_polytope
              (fun i : Fin m ↦ (weights i.castSucc : ℝ))
              (capacity : ℝ))
            alpha
            beta)).direction ≤
      Module.finrank ℝ
        (affineSpan ℝ
          (face_set
            (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
              last_coordinate_eq_set m 0)
            (Fin.snoc alpha 0)
            beta)).direction := by
  let oldFace : Set (Fin m → ℝ) :=
    face_set
      (zero_one_knapsack_polytope
        (fun i : Fin m ↦ (weights i.castSucc : ℝ))
        (capacity : ℝ))
      alpha
      beta
  let zeroSliceFace : Set (Fin (m + 1) → ℝ) :=
    face_set
      (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) ∩
        last_coordinate_eq_set m 0)
      (Fin.snoc alpha 0)
      beta
  let L := remark_7_5_snocZeroLinear m
  have himage : L '' oldFace ⊆ zeroSliceFace := by
    rintro z ⟨y, hy, rfl⟩
    exact remark_7_5_snocZero_mem_zeroSliceFace weights capacity alpha beta hy
  have hspan :
      affineSpan ℝ (L '' oldFace) =
        (affineSpan ℝ oldFace).map L.toAffineMap := by
    -- Affine span commutes with the linear zero-coordinate embedding.
    symm
    simpa using (AffineSubspace.map_span L.toAffineMap oldFace)
  have hmapRank :
      Module.finrank ℝ (affineSpan ℝ oldFace).direction =
        Module.finrank ℝ (affineSpan ℝ (L '' oldFace)).direction := by
    rw [hspan, AffineSubspace.map_direction]
    let e :
        (affineSpan ℝ oldFace).direction ≃ₗ[ℝ]
          Submodule.map L (affineSpan ℝ oldFace).direction :=
      Submodule.equivMapOfInjective
        L
        remark_7_5_snocZeroLinear_injective
        (affineSpan ℝ oldFace).direction
    exact LinearEquiv.finrank_eq e
  have hdirection :
      (affineSpan ℝ (L '' oldFace)).direction ≤
        (affineSpan ℝ zeroSliceFace).direction :=
    AffineSubspace.direction_le (affineSpan_mono ℝ himage)
  -- Injectivity preserves the old dimension, and affine-span monotonicity supplies the bound.
  calc
    Module.finrank ℝ (affineSpan ℝ oldFace).direction =
        Module.finrank ℝ (affineSpan ℝ (L '' oldFace)).direction := hmapRank
    _ ≤ Module.finrank ℝ (affineSpan ℝ zeroSliceFace).direction :=
      Submodule.finrank_mono hdirection

/-- Helper for Remark 7.5: once the previous prefix stage is facet-defining, the strengthened
upper bound should promote the successor stage to a facet by one Proposition 7.2 step. -/
private theorem remark_7_5_successorFacetOfUpperBound
    {m t : ℕ}
    (weights : Fin (m + 1) → ℕ)
    (capacity : ℕ)
    (ht : t ≤ m)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := m + 1) t))
    (hdescending :
      remark_7_5_cover_weights_descending weights (Nat.le_trans ht (Nat.le_succ m)))
    (h : Fin (m + 1) → ℕ)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h)
    (lam : ℕ)
    (hlam :
      lam =
        remark_7_5_cover_excess
          weights
          capacity
          t
          (Nat.le_trans ht (Nat.le_succ m)))
    (hupper :
      remark_7_5_strong_upper_bound
        weights
        (remark_7_5_cover (n := m + 1) t)
        (remark_7_5_mu weights t (Nat.le_trans ht (Nat.le_succ m)))
        h
        lam)
    (hfacetPrev :
      remark_7_5_lifting_coeff
          (remark_7_5_cover (n := m) t)
          (fun i : Fin m ↦ h i.castSucc) ∈
        facet_defining_liftings_of_cover_inequality
          (fun j : Fin m ↦ (weights j.castSucc : ℝ))
          (capacity : ℝ)
          (remark_7_5_cover (n := m) t)) :
    remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        (remark_7_5_cover (n := m + 1) t) := by
  -- Route correction: the remaining work is now purely the zero-slice facet transport plus the
  -- Proposition 7.2 dimension jump, with `hlam` available for the final coefficient rewrite.
  let S := zero_one_knapsack_set (fun j ↦ (weights j : ℝ)) (capacity : ℝ)
  let P := convexHull ℝ S
  let oldP :=
    zero_one_knapsack_polytope
      (fun j : Fin m ↦ (weights j.castSucc : ℝ))
      (capacity : ℝ)
  let alphaPrev : Fin m → ℝ :=
    remark_7_5_lifting_coeff
      (remark_7_5_cover (n := m) t)
      (fun i : Fin m ↦ h i.castSucc)
  let beta := cover_inequality_rhs (remark_7_5_cover (n := m + 1) t)
  let coeff := last_coordinate_lifting_coefficient S alphaPrev beta
  let oldFace : Set (Fin m → ℝ) := face_set oldP alphaPrev beta
  let zeroSliceFace : Set (Fin (m + 1) → ℝ) :=
    face_set
      (P ∩ last_coordinate_eq_set m 0)
      (Fin.snoc alphaPrev 0)
      beta
  let liftedFace : Set (Fin (m + 1) → ℝ) :=
    face_set
      P
      (remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h)
      beta
  have hbetaEq :
      cover_inequality_rhs (remark_7_5_cover (n := m) t) = beta := by
    -- Consecutive ambient prefix stages contain the same `t` cover coordinates.
    simp [beta, cover_inequality_rhs_eq,
      remark_7_5_cover_card (n := m) t ht,
      remark_7_5_cover_card (n := m + 1) t (Nat.le_trans ht (Nat.le_succ m))]
  have hfacetOldRaw :=
    (mem_facet_defining_liftings_of_cover_inequality_iff).mp hfacetPrev
  rw [lifted_cover_face, remark_7_5_liftingCoeff_idempotent] at hfacetOldRaw
  have hfacetOld : IsFacetOf oldP oldFace := by
    -- Normalize the old right-hand side to the current stage's unchanged cover right-hand side.
    simpa [oldP, oldFace, alphaPrev, hbetaEq] using hfacetOldRaw
  rcases (isFacetOf_iff.mp hfacetOld) with
    ⟨holdFaceNonempty, holdFaceExposed, holdFaceCodim⟩
  have holdWeightsNonnegative :
      ∀ j : Fin m, 0 ≤ (weights j.castSucc : ℝ) := by
    intro j
    positivity
  have hcapacityNonnegative : (0 : ℝ) ≤ capacity := by
    positivity
  have holdOverweight :
      zero_one_knapsack_overweight_indices
          (fun j : Fin m ↦ (weights j.castSucc : ℝ))
          (capacity : ℝ) = ∅ := by
    ext j
    simp [zero_one_knapsack_overweight_indices, hweights_le j.castSucc]
  have holdPolytopeDim :
      Module.finrank ℝ (affineSpan ℝ oldP).direction = m := by
    -- No old coordinate is overweight, so the previous knapsack polytope is full-dimensional.
    simpa [oldP, holdOverweight] using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        (fun j : Fin m ↦ (weights j.castSucc : ℝ))
        (capacity : ℝ)
        holdWeightsNonnegative
        hcapacityNonnegative
  have holdFaceCodimM :
      Module.finrank ℝ (affineSpan ℝ oldFace).direction + 1 = m := by
    rw [holdFaceCodim, holdPolytopeDim]
  have hzeroSliceFaceNonempty : zeroSliceFace.Nonempty := by
    rcases holdFaceNonempty with ⟨y, hy⟩
    refine ⟨Fin.snoc y 0, ?_⟩
    simpa [zeroSliceFace, P, S, oldFace, oldP, alphaPrev, beta,
      zero_one_knapsack_polytope_eq_convexHull] using
      remark_7_5_snocZero_mem_zeroSliceFace weights capacity alphaPrev beta hy
  have holdDimLeZeroSliceDim :
      Module.finrank ℝ (affineSpan ℝ oldFace).direction ≤
        Module.finrank ℝ (affineSpan ℝ zeroSliceFace).direction := by
    -- The local snoc-zero interface transfers the previous face dimension to the zero slice.
    simpa [zeroSliceFace, P, S, oldFace, oldP, alphaPrev, beta,
      zero_one_knapsack_polytope_eq_convexHull] using
      remark_7_5_oldFace_finrank_le_zeroSliceFace weights capacity alphaPrev beta
  have hcastBounds :=
    remark_7_5_castSuccWeightBounds weights capacity hweights_pos hweights_le
  have hvalidPrev :
      is_valid_inequality
        (zero_one_knapsack_set
          (fun j : Fin m ↦ (weights j.castSucc : ℝ))
          (capacity : ℝ))
        alphaPrev
        beta := by
    -- Rebuild old-stage validity with the normalized current right-hand side.
    have hvalidOld :=
      remark_7_5_setValidOfIntervalIndicesNormalized
        (fun j : Fin m ↦ weights j.castSucc)
        capacity
        t
        ht
        hcastBounds.1
        hcastBounds.2
        (remark_7_5_minimalCover_castSucc capacity ht weights hCmin)
        (remark_7_5_coverWeightsDescending_castSucc ht weights hdescending)
        (fun j : Fin m ↦ h j.castSucc)
        (remark_7_5_intervalIndices_castSucc ht weights h hinterval)
    simpa [alphaPrev, hbetaEq] using hvalidOld
  have hvalidZero :
      is_valid_inequality
        (S ∩ last_coordinate_eq_set m 0)
        (Fin.snoc alphaPrev 0)
        beta := by
    have hvalidPrevInS :
        is_valid_inequality
          (zero_one_knapsack_set
            (fun i : Fin m ↦ (weights i.castSucc : ℝ))
            (capacity : ℝ))
          alphaPrev
          beta := by
      simpa [S] using hvalidPrev
    exact
      remark_7_5_lastCoordinateZeroSliceValid
        weights
        capacity
        alphaPrev
        beta
        hvalidPrevInS
  have hSBinary :
      S ⊆ zero_one_points (Nat.le_refl (m + 1)) (Set.univ : Set (Fin (m + 1) → ℝ)) := by
    simpa [S] using
      remark_7_5_zeroOneKnapsackSet_subset_zeroOnePointsUniv weights capacity
  have hlastSingletonValue :
      (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) (Fin.last m) = 1 := by
    simp
  have honeSliceNonempty : Set.Nonempty (S ∩ last_coordinate_eq_set m 1) := by
    -- The feasible singleton at the new coordinate supplies the required one-slice point.
    refine ⟨Pi.single (Fin.last m) (1 : ℝ), ?_⟩
    refine ⟨?_, mem_last_coordinate_eq_set_iff.mpr hlastSingletonValue⟩
    simpa [S] using remark_7_5_lastSingletonFeasible weights capacity hweights_le
  have hcoeffEq : coeff = h (Fin.last m) := by
    -- The strengthened interval bound identifies Proposition 7.2's maximal coefficient.
    exact
      remark_7_5_stageLastCoefficientEq
        weights
        capacity
        ht
        hweights_pos
        hweights_le
        hCmin
        hdescending
        h
        hinterval
        lam
        hlam
        hupper
  have hcoeffVectorEq :
      Fin.snoc alphaPrev coeff =
        remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h := by
    rw [hcoeffEq]
    exact (remark_7_5_liftingCoeff_snoc ht h).symm
  let d := Module.finrank ℝ (affineSpan ℝ zeroSliceFace).direction
  have hzeroSliceDim :
      Module.finrank ℝ
          (affineSpan ℝ
            (face_set
              (convexHull ℝ S ∩ last_coordinate_eq_set m 0)
              (Fin.snoc alphaPrev 0)
              beta)).direction = d := by
    rfl
  have hzeroSliceFaceNonemptyForStep :
      Set.Nonempty
        (face_set
          (convexHull ℝ S ∩ last_coordinate_eq_set m 0)
          (Fin.snoc alphaPrev 0)
          beta) := by
    simpa [zeroSliceFace, P] using hzeroSliceFaceNonempty
  have hdimensionStepRaw :=
    binary_last_coordinate_lifting_face_dimension_lower_bound
      S
      alphaPrev
      beta
      d
      hSBinary
      hvalidZero
      honeSliceNonempty
      hzeroSliceFaceNonemptyForStep
      hzeroSliceDim
  rw [hcoeffVectorEq] at hdimensionStepRaw
  have hdimensionStep :
      IsExposed ℝ P liftedFace ∧
        d + 1 ≤ Module.finrank ℝ (affineSpan ℝ liftedFace).direction := by
    simpa [P, liftedFace] using hdimensionStepRaw
  have hliftedFaceDimLower :
      m ≤ Module.finrank ℝ (affineSpan ℝ liftedFace).direction := by
    -- The previous facet contributes `m - 1` directions and Proposition 7.2 adds one more.
    dsimp [d] at hdimensionStep
    omega
  rcases
      remark_7_5_lastCoordinateTightWitness
        weights
        capacity
        ht
        hweights_pos
        hCmin
        h
        hinterval
        lam
        hlam
        hupper with
    ⟨x, hxS, hxlast, hxpartial⟩
  have hxpartialNormalized :
      partial_lifting_value alphaPrev x = beta - h (Fin.last m) := by
    simpa [alphaPrev, beta] using hxpartial
  have hxTight :
      remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h ⬝ᵥ x = beta := by
    rw [remark_7_5_liftingCoeff_snoc ht h, dotProduct_last_coordinate_lifting_coeffs,
      hxlast, hxpartialNormalized]
    ring
  have hliftedFaceNonempty : liftedFace.Nonempty := by
    -- The strengthened-bound witness is a concrete tight point of the lifted face.
    refine ⟨x, (mem_face_set_iff).2 ⟨?_, hxTight⟩⟩
    exact subset_convexHull ℝ S hxS
  have htTwo : 2 ≤ t := by
    have hcoverTwo :=
      cover_card_ge_two
        weights
        capacity
        hweights_le
        (remark_7_5_cover (n := m + 1) t)
        hCmin.toIsKnapsackCover
    simpa [remark_7_5_cover_card (n := m + 1) t
      (Nat.le_trans ht (Nat.le_succ m))] using hcoverTwo
  have hzeroIndexLt : (0 : Fin (m + 1)) < t := by
    have hzeroLtTwo : 0 < 2 := by
      norm_num
    simpa using (lt_of_lt_of_le hzeroLtTwo htTwo)
  have hzeroIndexMem : (0 : Fin (m + 1)) ∈ remark_7_5_cover t :=
    remark_7_5_cover_mem_iff.mpr hzeroIndexLt
  have hzeroCoeff :
      remark_7_5_lifting_coeff
          (remark_7_5_cover (n := m + 1) t) h 0 = 1 := by
    exact remark_7_5_lifting_coeff_apply_of_mem hzeroIndexMem
  have hliftedFaceCodimUpper :
      Module.finrank ℝ (affineSpan ℝ liftedFace).direction + 1 ≤ m + 1 := by
    simpa [liftedFace, P] using
      remark_7_5_faceSet_finrank_add_one_le
        (P := P)
        (c := remark_7_5_lifting_coeff (remark_7_5_cover (n := m + 1) t) h)
        (β := beta)
        0
        hzeroCoeff
        hliftedFaceNonempty
  have hliftedFaceDim :
      Module.finrank ℝ (affineSpan ℝ liftedFace).direction = m := by
    omega
  have hcurrentWeightsNonnegative : ∀ j, 0 ≤ (weights j : ℝ) := by
    intro j
    positivity
  have hcurrentOverweight :
      zero_one_knapsack_overweight_indices
          (fun j ↦ (weights j : ℝ))
          (capacity : ℝ) = ∅ := by
    ext j
    simp [zero_one_knapsack_overweight_indices, hweights_le j]
  have hpolytopeDim :
      Module.finrank ℝ (affineSpan ℝ P).direction = m + 1 := by
    -- The current polytope is likewise full-dimensional because every item fits individually.
    simpa [P, S, zero_one_knapsack_polytope_eq_convexHull, hcurrentOverweight] using
      zero_one_knapsack_polytope_finrank_direction_affineSpan
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        hcurrentWeightsNonnegative
        hcapacityNonnegative
  have hliftedFaceCodim :
      Module.finrank ℝ (affineSpan ℝ liftedFace).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ P).direction := by
    rw [hliftedFaceDim, hpolytopeDim]
  refine (mem_facet_defining_liftings_of_cover_inequality_iff).2 ?_
  rw [lifted_cover_face, remark_7_5_liftingCoeff_idempotent]
  simpa [P, S, liftedFace, beta, zero_one_knapsack_polytope_eq_convexHull] using
    (isFacetOf_iff).2
      ⟨hliftedFaceNonempty, hdimensionStep.1, hliftedFaceCodim⟩

/-- Helper for Remark 7.5: in normalized prefix form, the strengthened upper bound upgrades the
canonical lifting to the facet-defining owner by the same stage induction. -/
private theorem remark_7_5_coverFacetMembershipOfUpperBoundNormalized
    (weights : Fin n → ℕ)
    (capacity t : ℕ)
    (ht : t ≤ n)
    (hdescending : remark_7_5_cover_weights_descending weights ht)
    (hweights_pos : ∀ j, 0 < weights j)
    (hweights_le : ∀ j, weights j ≤ capacity)
    (hCmin : IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := n) t))
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hlam : lam = remark_7_5_cover_excess weights capacity t ht)
    (hinterval :
      remark_7_5_interval_indices
        weights
        (remark_7_5_cover (n := n) t)
        (remark_7_5_mu weights t ht)
        h)
    (hupper :
      remark_7_5_strong_upper_bound
        weights
        (remark_7_5_cover (n := n) t)
        (remark_7_5_mu weights t ht)
        h
        lam) :
    remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        (remark_7_5_cover (n := n) t) := by
  rcases Nat.exists_eq_add_of_le ht with ⟨m, rfl⟩
  -- Route correction: the facet proof now follows the same prefix-stage induction as validity.
  let go :
      ∀ m : ℕ,
        ∀ weights : Fin (t + m) → ℕ,
          remark_7_5_cover_weights_descending weights (Nat.le_add_right t m) →
          (∀ j, 0 < weights j) →
          (∀ j, weights j ≤ capacity) →
          IsMinimalKnapsackCover weights capacity (remark_7_5_cover (n := t + m) t) →
          ∀ h : Fin (t + m) → ℕ,
            remark_7_5_interval_indices
              weights
              (remark_7_5_cover (n := t + m) t)
              (remark_7_5_mu weights t (Nat.le_add_right t m))
              h →
            ∀ lam : ℕ,
            lam = remark_7_5_cover_excess weights capacity t (Nat.le_add_right t m) →
            remark_7_5_strong_upper_bound
              weights
              (remark_7_5_cover (n := t + m) t)
              (remark_7_5_mu weights t (Nat.le_add_right t m))
              h
              lam →
              remark_7_5_lifting_coeff (remark_7_5_cover (n := t + m) t) h ∈
                facet_defining_liftings_of_cover_inequality
                  (fun j ↦ (weights j : ℝ))
                  (capacity : ℝ)
                  (remark_7_5_cover (n := t + m) t) := by
    intro m
    induction m with
    | zero =>
        intro weights hdescending hweights_pos hweights_le hCmin h hinterval lam hlam hupper
        have hctx :
            remark_7_5_theorem_7_4_context
              weights
              capacity
              (remark_7_5_cover (n := t) t)
              (remark_7_5_mu weights t (Nat.le_refl t))
              (remark_7_5_cover_excess weights capacity t (Nat.le_refl t)) := by
          refine ⟨t, Nat.le_refl t, rfl, ?_, hweights_pos, hweights_le, hCmin, rfl, rfl⟩
          · simpa using hdescending
        simpa using remark_7_5_univCoverFacetMembership weights capacity h hctx
    | succ m ih =>
        intro weights hdescending hweights_pos hweights_le hCmin h hinterval lam hlam hupper
        have hcastBounds :=
          remark_7_5_castSuccWeightBounds weights capacity hweights_pos hweights_le
        have hlamPrev :
            lam =
              remark_7_5_cover_excess
                (fun j : Fin (t + m) ↦ weights j.castSucc)
                capacity
                t
                (Nat.le_add_right t m) := by
          simpa [remark_7_5_coverExcess_castSucc_eq (Nat.le_add_right t m) weights capacity] using
            hlam
        have hfacetPrev :
            remark_7_5_lifting_coeff
                (remark_7_5_cover (n := t + m) t)
                (fun i : Fin (t + m) ↦ h i.castSucc) ∈
              facet_defining_liftings_of_cover_inequality
                (fun j : Fin (t + m) ↦ (weights j.castSucc : ℝ))
                (capacity : ℝ)
                (remark_7_5_cover (n := t + m) t) := by
          exact
            ih
              (fun j : Fin (t + m) ↦ weights j.castSucc)
              (remark_7_5_coverWeightsDescending_castSucc
                (Nat.le_add_right t m)
                weights
                hdescending)
              hcastBounds.1
              hcastBounds.2
              (remark_7_5_minimalCover_castSucc
                capacity
                (Nat.le_add_right t m)
                weights
                hCmin)
              (fun j : Fin (t + m) ↦ h j.castSucc)
              (remark_7_5_intervalIndices_castSucc
                (Nat.le_add_right t m)
                weights
                h
                hinterval)
              lam
              hlamPrev
              (remark_7_5_strongUpperBound_castSucc
                (Nat.le_add_right t m)
                weights
                h
                lam
                hupper)
        exact
          remark_7_5_successorFacetOfUpperBound
            weights
            capacity
            (Nat.le_add_right t m)
            hweights_pos
            hweights_le
            hCmin
            hdescending
            h
            hinterval
            lam
            hlam
            hupper
            hfacetPrev
  exact go m weights hdescending hweights_pos hweights_le hCmin h hinterval lam hlam hupper

/-- Helper for Remark 7.5: the strengthened upper bound should upgrade the interval-index lifting
to the Chapter 7.1 facet-defining cover-lifting owner. -/
private theorem remark_7_5_coverFacetMembershipOfUpperBound
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam) :
    remark_7_5_lifting_coeff C h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        C := by
  rcases hctx with ⟨t, ht, rfl, hdescending, hweights_pos, hweights_le, hCmin, rfl, hlam⟩
  -- Route correction: the remaining blocker is now isolated in the successor-stage facet step.
  exact
    remark_7_5_coverFacetMembershipOfUpperBoundNormalized
      weights
      capacity
      t
      ht
      hdescending
      hweights_pos
      hweights_le
      hCmin
      h
      lam
      hlam
      hinterval
      hupper

/-- Helper for Remark 7.5: every coordinate of a point in the `0,1` knapsack polytope lies in the
unit interval. -/
private theorem remark_7_5_knapsackPolytopeCoordBounds
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
    -- On binary points, the lower bound is exactly `-x_j ≤ 0`.
    intro y hy
    rw [mem_zero_one_knapsack_set_iff] at hy
    rcases hy.1 j with hyj | hyj
    · simp [hyj, dotProduct, Pi.single_apply]
    · simp [hyj, dotProduct, Pi.single_apply]
  have hupper_set :
      is_valid_inequality
        (zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Pi.single j (1 : ℝ))
        1 := by
    -- On binary points, the upper bound is exactly `x_j ≤ 1`.
    intro y hy
    rw [mem_zero_one_knapsack_set_iff] at hy
    rcases hy.1 j with hyj | hyj
    · simp [hyj, dotProduct, Pi.single_apply]
    · simp [hyj, dotProduct, Pi.single_apply]
  have hlower_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (-Pi.single j (1 : ℝ))
        0 := by
    -- Validity passes from the binary set to the convex-hull polytope.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hlower_set
  have hupper_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (Pi.single j (1 : ℝ))
        1 := by
    -- Validity passes from the binary set to the convex-hull polytope.
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact is_valid_inequality_convexHull_iff.mpr hupper_set
  refine ⟨?_, ?_⟩
  · -- Evaluate the lower-bound inequality at `x`.
    have hxlower := hlower_poly hx
    simpa [dotProduct, Pi.single_apply] using hxlower
  · -- Evaluate the upper-bound inequality at `x`.
    have hxupper := hupper_poly hx
    simpa [dotProduct, Pi.single_apply] using hxupper

/-- Helper for Remark 7.5: if one facet face of the knapsack polytope is contained in another,
then the two faces coincide. -/
private theorem remark_7_5_facet_eq_of_subset
    {P F H : Set (Fin n → ℝ)}
    (hF : IsFacetOf P F)
    (hH : IsFacetOf P H)
    (hsubset : F ⊆ H) :
    F = H := by
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  rcases hH with ⟨hH_nonempty, hH_exposed, hH_codim⟩
  obtain ⟨xF, hxF⟩ := hF_nonempty
  have hxFH : xF ∈ H := hsubset hxF
  have hdim_eq :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (affineSpan ℝ H).direction := by
    omega
  have h_aff_le : affineSpan ℝ F ≤ affineSpan ℝ H := affineSpan_mono ℝ hsubset
  have hdir_eq :
      (affineSpan ℝ F).direction = (affineSpan ℝ H).direction := by
    exact Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h_aff_le) hdim_eq
  have hspan_eq :
      affineSpan ℝ F = affineSpan ℝ H := by
    -- Equal directions and a common point identify the two affine spans.
    refine (AffineSubspace.eq_iff_direction_eq_of_mem
      (subset_affineSpan ℝ _ hxF) (subset_affineSpan ℝ _ hxFH)).2 hdir_eq
  obtain ⟨l, hF_eq⟩ := hF_exposed ⟨xF, hxF⟩
  have hxF_face : xF ∈ l.toExposed P := by
    simpa [hF_eq] using hxF
  have hxF_mem : xF ∈ P := hxF_face.1
  have hxF_max : ∀ y, y ∈ P → l y ≤ l xF := hxF_face.2
  have hlevel : ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → l x = l xF := by
    intro x hx
    have hx_face : x ∈ l.toExposed P := by
      simpa [hF_eq] using hx
    exact le_antisymm (hxF_max x hx_face.1) (hx_face.2 xF hxF_mem)
  have hlevel_aff :
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ affineSpan ℝ F → l x = l xF := by
    intro x hx
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun y : Fin n → ℝ ↦ l y = l xF)
      hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro c u v w hu hv hw
      -- The exposing functional stays constant on the whole affine span of `F`.
      change l (c • (u - v) + w) = l xF
      calc
        l (c • (u - v) + w) = c * (l u - l v) + l w := by
            simp [map_add, map_sub]
        _ = l xF := by
            simp [hu, hv, hw]
  ext x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx_aff : x ∈ affineSpan ℝ F := by
      simpa [hspan_eq] using subset_affineSpan ℝ H hx
    have hx_level : l x = l xF := hlevel_aff hx_aff
    have hx_exposed : x ∈ l.toExposed P := by
      refine ⟨hH_exposed.subset hx, ?_⟩
      intro y hy
      calc
        l y ≤ l xF := hxF_max y hy
        _ = l x := hx_level.symm
    simpa [hF_eq] using hx_exposed

/-- Helper for Remark 7.5: coefficientwise domination on `N \ C` forces the old lifted-cover face
to lie inside the canonical face. -/
private theorem remark_7_5_faceSubset_of_offCoverCoeff_le
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    (hhvalid :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (remark_7_5_lifting_coeff C h)
        (cover_inequality_rhs C))
    {α : Fin n → ℝ}
    (hle : ∀ j, j ∉ C → α j ≤ h j) :
    lifted_cover_face
        (fun i ↦ (weights i : ℝ))
        (capacity : ℝ)
        C
        α ⊆
      lifted_cover_face
        (fun i ↦ (weights i : ℝ))
        (capacity : ℝ)
        C
        (fun j ↦ (h j : ℝ)) := by
  intro x hx
  rcases (mem_lifted_cover_face_iff.mp hx) with ⟨hxP, hxEqα⟩
  have hsum_le :
      Finset.sum (Finset.univ \ C) (fun j ↦ α j * x j) ≤
        Finset.sum (Finset.univ \ C) (fun j ↦ (h j : ℝ) * x j) := by
    -- Every off-cover coefficient of `α` is bounded above by the remark coefficient `h(j)`.
    refine Finset.sum_le_sum ?_
    intro j hj
    have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
    exact
      mul_le_mul_of_nonneg_right
        (hle j hjC)
        (remark_7_5_knapsackPolytopeCoordBounds weights capacity hxP j).1
  have hrhs_le :
      cover_inequality_rhs C ≤
        Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ (h j : ℝ) * x j) := by
    calc
      cover_inequality_rhs C
          = Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ α j * x j) := hxEqα.symm
      _ ≤ Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ (h j : ℝ) * x j) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hsum_le (Finset.sum C x)
  have hrhs_ge :
      Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ (h j : ℝ) * x j) ≤
        cover_inequality_rhs C := by
    -- Validity of the canonical Remark 7.5 inequality bounds the larger coefficient vector.
    simpa [remark_7_5_lifting_coeff_dotProduct] using hhvalid hxP
  exact (mem_lifted_cover_face_iff).2 ⟨hxP, le_antisymm hrhs_ge hrhs_le⟩

/-- Helper for Remark 7.5: if the canonical coefficient at `j` is strictly larger than `α j`,
then every point on the `α`-face has `x j = 0`. -/
private theorem remark_7_5_faceCoordinateZero_of_strictGap
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (h : Fin n → ℕ)
    {α : Fin n → ℝ}
    (hhvalid :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (remark_7_5_lifting_coeff C h)
        (cover_inequality_rhs C))
    (hle : ∀ k, k ∉ C → α k ≤ h k)
    {j : Fin n}
    (hj : j ∉ C)
    (hstrict : α j < h j) :
    ∀ ⦃x : Fin n → ℝ⦄,
      x ∈ lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) C α →
        x j = 0 := by
  intro x hx
  rcases (mem_lifted_cover_face_iff.mp hx) with ⟨hxP, hxEqα⟩
  let diffTerm : Fin n → ℝ := fun k ↦ ((h k : ℝ) - α k) * x k
  have hdiff_nonneg :
      ∀ k ∈ Finset.univ \ C, 0 ≤ diffTerm k := by
    intro k hk
    have hkC : k ∉ C := (Finset.mem_sdiff.mp hk).2
    exact
      mul_nonneg
        (sub_nonneg.mpr (hle k hkC))
        (remark_7_5_knapsackPolytopeCoordBounds weights capacity hxP k).1
  have hcanonical_decomp :
      Finset.sum C x + Finset.sum (Finset.univ \ C) (fun k ↦ (h k : ℝ) * x k) =
        (Finset.sum C x + Finset.sum (Finset.univ \ C) (fun k ↦ α k * x k)) +
          Finset.sum (Finset.univ \ C) diffTerm := by
    -- Rewrite the larger lifted sum as the old face value plus the nonnegative coefficient gap.
    calc
      Finset.sum C x + Finset.sum (Finset.univ \ C) (fun k ↦ (h k : ℝ) * x k)
          = Finset.sum C x +
              Finset.sum (Finset.univ \ C) (fun k ↦ α k * x k + diffTerm k) := by
                congr 1
                apply Finset.sum_congr rfl
                intro k hk
                dsimp [diffTerm]
                ring
      _ = (Finset.sum C x + Finset.sum (Finset.univ \ C) (fun k ↦ α k * x k)) +
            Finset.sum (Finset.univ \ C) diffTerm := by
              rw [Finset.sum_add_distrib]
              ring
  have hcanonical_le :
      Finset.sum C x + Finset.sum (Finset.univ \ C) (fun k ↦ (h k : ℝ) * x k) ≤
        cover_inequality_rhs C := by
    -- The canonical valid inequality bounds every point of the ambient knapsack polytope.
    simpa [remark_7_5_lifting_coeff_dotProduct] using hhvalid hxP
  have hdiff_le_zero :
      Finset.sum (Finset.univ \ C) diffTerm ≤ 0 := by
    rw [hcanonical_decomp, hxEqα] at hcanonical_le
    linarith
  have hdiff_eq_zero :
      Finset.sum (Finset.univ \ C) diffTerm = 0 := by
    have hdiff_nonneg_sum :
        0 ≤ Finset.sum (Finset.univ \ C) diffTerm :=
      Finset.sum_nonneg fun k hk ↦ hdiff_nonneg k hk
    linarith
  have hj_mem : j ∈ Finset.univ \ C := by
    simp [hj]
  have hterm_le_sum :
      diffTerm j ≤ Finset.sum (Finset.univ \ C) diffTerm := by
    exact Finset.single_le_sum (fun k hk ↦ hdiff_nonneg k hk) hj_mem
  have hterm_eq_zero : diffTerm j = 0 := by
    have hterm_nonneg : 0 ≤ diffTerm j := hdiff_nonneg j hj_mem
    linarith
  by_cases hxj : x j = 0
  · exact hxj
  · have hxj_nonneg : 0 ≤ x j := (remark_7_5_knapsackPolytopeCoordBounds weights capacity hxP j).1
    have hxj_pos : 0 < x j := lt_of_le_of_ne hxj_nonneg (Ne.symm hxj)
    have hgap_pos : 0 < (h j : ℝ) - α j := sub_pos.mpr hstrict
    have hterm_pos : 0 < diffTerm j := by
      dsimp [diffTerm]
      exact mul_pos hgap_pos hxj_pos
    linarith

/-- Helper for Remark 7.5: under the strengthened upper bound, the canonical lifted-cover face
contains a tight point with the chosen off-cover coordinate equal to `1`. -/
private theorem remark_7_5_canonicalFaceWitness
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {j : Fin n}
    (hj : j ∉ C) :
    ∃ x : Fin n → ℝ,
      x ∈
        lifted_cover_face
          (fun i ↦ (weights i : ℝ))
          (capacity : ℝ)
          C
          (fun k ↦ (h k : ℝ)) ∧
        x j = 1 := by
  rcases hctx with ⟨t, ht, rfl, hdescending, hweights_pos, hweights_le, hCmin, rfl, rfl⟩
  have hs : h j + 1 ≤ t := by
    -- The interval condition forces the chosen index to occur before the cover sum stabilizes.
    by_contra hs
    have ht_le_hj : t ≤ h j := by
      omega
    have ht_le_hj_succ : t ≤ h j + 1 := by
      omega
    have hμhj :
        remark_7_5_mu weights t ht (h j) = remark_7_5_mu weights t ht t :=
      remark_7_5_mu_eq_of_ge weights t ht (h j) ht_le_hj
    have hμhjsucc :
        remark_7_5_mu weights t ht (h j + 1) = remark_7_5_mu weights t ht t :=
      remark_7_5_mu_eq_of_ge weights t ht (h j + 1) ht_le_hj_succ
    have hjinterval := hinterval j hj
    rw [hμhj, hμhjsucc] at hjinterval
    omega
  let x : Fin n → ℝ := remark_7_5_suffixWitness t j (h j + 1)
  have hupperj :
      weights j ≤
        remark_7_5_mu weights t ht (h j + 1) -
          remark_7_5_cover_excess weights capacity t ht :=
    hupper j hj
  have hweight_nat :
      weights j +
          (remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht (h j + 1)) ≤
        capacity := by
    -- Normalize the strengthened upper bound to the suffix-witness feasibility inequality.
    have hposj : 0 < weights j := hweights_pos j
    have hcover_excess_lt :
        remark_7_5_cover_excess weights capacity t ht <
          remark_7_5_mu weights t ht (h j + 1) := by
      exact
        (Nat.sub_pos_iff_lt.mp <|
          lt_of_lt_of_le hposj hupperj)
    have hupperj_add :
        weights j + remark_7_5_cover_excess weights capacity t ht ≤
          remark_7_5_mu weights t ht (h j + 1) := by
      exact
        (Nat.le_sub_iff_add_le hcover_excess_lt.le).mp hupperj
    have hmu_prefix_le :
        remark_7_5_mu weights t ht (h j + 1) ≤ remark_7_5_mu weights t ht t := by
      have hs_le_n : h j + 1 ≤ n := Nat.le_trans hs ht
      have hprefix_sum_le :
          (remark_7_5_cover (n := n) (h j + 1)).sum weights ≤
            (remark_7_5_cover (n := n) t).sum weights :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (remark_7_5_cover_subset (n := n) hs)
          (by
            intro i hi hino
            exact Nat.zero_le _)
      have hprefix_sum_eq :
          (remark_7_5_cover (n := n) (h j + 1)).sum weights =
            remark_7_5_mu weights t ht (h j + 1) := by
        calc
          (remark_7_5_cover (n := n) (h j + 1)).sum weights
              = remark_7_5_mu weights (h j + 1) hs_le_n (h j + 1) := by
                  rw [remark_7_5_cover_sum_eq_mu]
          _ = remark_7_5_mu weights t ht (h j + 1) := by
                rw [remark_7_5_mu_prefix_eq weights hs_le_n ht hs]
      have hcover_sum_eq :
          (remark_7_5_cover (n := n) t).sum weights =
            remark_7_5_mu weights t ht t := by
        rw [remark_7_5_cover_sum_eq_mu]
      rw [hprefix_sum_eq, hcover_sum_eq] at hprefix_sum_le
      exact hprefix_sum_le
    simp only [ge_iff_le] at hupperj_add ⊢
    have hmu_t_ge_capacity :
        capacity ≤ remark_7_5_mu weights t ht t := by
      have hcover : IsKnapsackCover weights capacity (remark_7_5_cover (n := n) t) :=
        inferInstance
      have hcover_lt :
          capacity < (remark_7_5_cover (n := n) t).sum weights :=
        (isKnapsackCover_iff weights capacity (remark_7_5_cover (n := n) t)).mp hcover
      rw [remark_7_5_cover_sum_eq_mu weights t ht] at hcover_lt
      exact Nat.le_of_lt hcover_lt
    have hupperj_total :
        weights j + remark_7_5_mu weights t ht t ≤
          remark_7_5_mu weights t ht (h j + 1) + capacity := by
      have hupperj_add_capacity := Nat.add_le_add_right hupperj_add capacity
      calc
        weights j + remark_7_5_mu weights t ht t
            = weights j +
                ((remark_7_5_mu weights t ht t - capacity) + capacity) := by
                  rw [Nat.sub_add_cancel hmu_t_ge_capacity]
        _ = (weights j + (remark_7_5_mu weights t ht t - capacity)) + capacity := by
              omega
        _ ≤ remark_7_5_mu weights t ht (h j + 1) + capacity := hupperj_add_capacity
    have hmu_split :
        remark_7_5_mu weights t ht t =
          remark_7_5_mu weights t ht (h j + 1) +
            (remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht (h j + 1)) := by
      omega
    have hcombined :
        weights j +
            (remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht (h j + 1)) +
            remark_7_5_mu weights t ht (h j + 1) ≤
          remark_7_5_mu weights t ht (h j + 1) + capacity := by
      calc
        weights j +
            (remark_7_5_mu weights t ht t - remark_7_5_mu weights t ht (h j + 1)) +
            remark_7_5_mu weights t ht (h j + 1)
            = weights j + remark_7_5_mu weights t ht t := by
                rw [hmu_split]
                omega
        _ ≤ remark_7_5_mu weights t ht (h j + 1) + capacity := hupperj_total
    omega
  have hx_set :
      x ∈ zero_one_knapsack_set (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
    -- The explicit suffix witness is feasible exactly under the normalized residual inequality.
    refine
      remark_7_5_suffixWitnessFeasible
        weights capacity t ht hj (h j + 1) hs ?_
    exact_mod_cast hweight_nat
  have hx_poly :
      x ∈ zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ) := by
    rw [zero_one_knapsack_polytope_eq_convexHull]
    exact subset_convexHull ℝ _ hx_set
  have hx_eq :
      remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h ⬝ᵥ x =
        cover_inequality_rhs (remark_7_5_cover (n := n) t) := by
    -- The same witness saturates the canonical lifted inequality at equality.
    calc
      remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h ⬝ᵥ x
          =
            remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h ⬝ᵥ
              remark_7_5_suffixWitness t j (h j + 1) := by
                rfl
      _ = remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h j +
            ((t - (h j + 1 : ℕ)) : ℝ) := by
              refine
                remark_7_5_suffixWitnessCoeff
                  (t := t)
                  (ht := ht)
                  (α := remark_7_5_lifting_coeff (remark_7_5_cover (n := n) t) h)
                  ?_
                  hj
                  (h j + 1)
                  hs
              intro i hi
              simpa using
                remark_7_5_lifting_coeff_apply_of_mem
                  (C := remark_7_5_cover (n := n) t)
                  (h := h)
                  hi
      _ = (h j : ℝ) + ((t - (h j + 1 : ℕ)) : ℝ) := by
            simp [remark_7_5_lifting_coeff_apply_of_not_mem hj]
      _ = cover_inequality_rhs (remark_7_5_cover (n := n) t) := by
            rw [cover_inequality_rhs_eq, remark_7_5_cover_card (n := n) t ht]
            norm_num
            ring
  have hxj : x j = 1 := by
    -- The witness explicitly turns on the chosen pivot coordinate.
    simp [x, remark_7_5_suffixWitness, remark_7_5_suffixWitnessSupport]
  refine ⟨x, ?_, hxj⟩
  refine (mem_lifted_cover_face_iff).2 ⟨hx_poly, ?_⟩
  simpa [remark_7_5_lifting_coeff_dotProduct] using hx_eq

/-- Helper for Remark 7.5: every facet-defining lifting should match the remark coefficients on
coordinates outside the cover. -/
private theorem remark_7_5_offCoverEqOfMemFacetDefining
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {α : Fin n → ℝ}
    (hα : α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C)
    {j : Fin n}
    (hj : j ∉ C) :
    α j = (h j : ℝ) := by
  have hαvalid :
      α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C :=
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hα).1
  have hhvalid_poly :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ))
        (remark_7_5_lifting_coeff C h)
        (cover_inequality_rhs C) := by
    -- Use the already-packaged binary-set validity and pass to the convex hull owner.
    exact
      remark_7_5_polytopeValid_of_setValid
        (fun i ↦ (weights i : ℝ))
        (capacity : ℝ)
        (remark_7_5_lifting_coeff C h)
        (cover_inequality_rhs C)
        (remark_7_5_setValidOfIntervalIndices weights capacity C μ h ⟨lam, hctx⟩ hinterval)
  have hcoeff_le :
      ∀ k, k ∉ C → α k ≤ h k := by
    intro k hk
    exact
      remark_7_5_coeff_le_of_mem_validLifting
        weights capacity C μ h lam hctx hupper hαvalid hk
  let P :=
    zero_one_knapsack_polytope (fun i ↦ (weights i : ℝ)) (capacity : ℝ)
  let Fα :=
    lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) C α
  let Fh :=
    lifted_cover_face (fun i ↦ (weights i : ℝ)) (capacity : ℝ) C (fun k ↦ (h k : ℝ))
  have hsubset : Fα ⊆ Fh := by
    -- Any face point for `α` also satisfies the canonical remark inequality at equality.
    exact
      remark_7_5_faceSubset_of_offCoverCoeff_le
        weights capacity C h hhvalid_poly hcoeff_le
  have hfacetα : IsFacetOf P Fα := by
    -- The given lifting is facet-defining by hypothesis.
    simpa [P, Fα] using
      (mem_facet_defining_liftings_of_cover_inequality_iff.mp
        (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hα).2)
  have hfaceth : IsFacetOf P Fh := by
    -- The canonical remark lifting is also facet-defining under the stronger upper bound.
    have hfaceth_raw :
        IsFacetOf P
          (lifted_cover_face
            (fun i ↦ (weights i : ℝ))
            (capacity : ℝ)
            C
            (remark_7_5_lifting_coeff C h)) := by
      simpa [P] using
        (mem_facet_defining_liftings_of_cover_inequality_iff.mp
          (remark_7_5_coverFacetMembershipOfUpperBound
            weights capacity C μ h lam hctx hinterval hupper))
    have hface_eq :
        lifted_cover_face
            (fun i ↦ (weights i : ℝ))
            (capacity : ℝ)
            C
            (remark_7_5_lifting_coeff C h) = Fh := by
      have hcoeff_eq :
          lifted_cover_inequality_coeff C (remark_7_5_lifting_coeff C h) =
            lifted_cover_inequality_coeff C (fun k ↦ (h k : ℝ)) := by
        funext i
        by_cases hi : i ∈ C
        · simp [lifted_cover_inequality_coeff, hi]
        · simp [remark_7_5_lifting_coeff, lifted_cover_inequality_coeff, hi]
      simp [Fh, lifted_cover_face, hcoeff_eq]
    simpa [hface_eq] using hfaceth_raw
  by_cases hEq : α j = (h j : ℝ)
  · exact hEq
  · have hstrict : α j < h j := lt_of_le_of_ne (hcoeff_le j hj) hEq
    have hzero_on_face :
        ∀ ⦃x : Fin n → ℝ⦄, x ∈ Fα → x j = 0 :=
      remark_7_5_faceCoordinateZero_of_strictGap
        weights capacity C h hhvalid_poly hcoeff_le hj hstrict
    have hface_eq : Fα = Fh :=
      remark_7_5_facet_eq_of_subset hfacetα hfaceth hsubset
    obtain ⟨xbar, hxbarFh, hxbarj⟩ :=
      remark_7_5_canonicalFaceWitness
        weights capacity C μ h lam hctx hinterval hupper hj
    have hxbarFα : xbar ∈ Fα := by
      simpa [hface_eq] using hxbarFh
    have hxbar_zero : xbar j = 0 := hzero_on_face hxbarFα
    linarith

/-- Remark 7.5 (1). Let `K` be the `0,1` knapsack set with weights `weights` and capacity
`capacity`, and let `C` and the partial sums `μ` come from the Theorem 7.4 setup.
If `h(j)` is chosen for each `j ∉ C` so that `μ_{h(j)} ≤ a_j < μ_{h(j)+1}`, then the inequality
`∑_{j ∈ C} x_j + ∑_{j ∈ N \ C} h(j) x_j ≤ |C| - 1`
is a lifting of the minimal cover inequality associated with `C`. -/
theorem remark_7_5_lifted_cover_inequality_is_lifting
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (hctx : ∃ lam, remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h) :
    remark_7_5_lifting_coeff C h ∈
      valid_liftings_of_minimal_cover_inequality weights capacity C := by
  rw [mem_valid_liftings_of_minimal_cover_inequality_iff]
  constructor
  · intro j hj
    -- The displayed lifting keeps the cover coefficients fixed by construction.
    simpa using remark_7_5_lifting_coeff_apply_of_mem (C := C) (h := h) hj
  · -- First prove validity on the binary knapsack set, then pass to the convex-hull polytope.
    exact
      remark_7_5_polytopeValid_of_setValid
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        (remark_7_5_lifting_coeff C h)
        (cover_inequality_rhs C)
        (remark_7_5_setValidOfIntervalIndices
          weights capacity C μ h hctx hinterval)

/-- Companion bridge: Remark 7.5 (1) gives the canonical valid-inequality owner on the knapsack
polytope. -/
theorem remark_7_5_lifting_coeff_is_valid_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (hctx : ∃ lam, remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h) :
    is_valid_inequality
      (zero_one_knapsack_polytope (fun j ↦ (weights j : ℝ)) (capacity : ℝ))
      (remark_7_5_lifting_coeff C h)
      (cover_inequality_rhs C) := by
  exact
    (mem_valid_liftings_of_minimal_cover_inequality_iff.mp
      (remark_7_5_lifted_cover_inequality_is_lifting
        weights capacity C μ h hctx hinterval)).2

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_remark_7_5.lean
— Remark 7.5 (2). If, in addition, `a_j ≤ μ_{h(j)+1} - λ` for every `j ∉ C`, then the lifted
inequality from Remark 7.5 is a facet-defining lifting of the minimal cover inequality attached
to the Theorem 7.4 cover `C`. -/
theorem remark_7_5_lifted_cover_inequality_is_facet_defining
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam) :
    remark_7_5_lifting_coeff C h ∈
      facet_defining_liftings_of_minimal_cover_inequality weights capacity C := by
  rw [mem_facet_defining_liftings_of_minimal_cover_inequality_iff]
  constructor
  · -- The facet statement already contains the valid-lifting part as its first component.
    exact remark_7_5_lifted_cover_inequality_is_lifting weights capacity C μ h ⟨lam, hctx⟩ hinterval
  · -- The strengthened upper bound should upgrade the valid lifting to a facet-defining one.
    exact
      remark_7_5_coverFacetMembershipOfUpperBound
        weights capacity C μ h lam hctx hinterval hupper

/-- Companion bridge: Remark 7.5 (2) places the displayed coefficient vector in the canonical
cover-lifting facet owner. -/
theorem remark_7_5_lifting_coeff_mem_facet_defining_liftings_of_cover_inequality
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam) :
    remark_7_5_lifting_coeff C h ∈
      facet_defining_liftings_of_cover_inequality
        (fun j ↦ (weights j : ℝ))
        (capacity : ℝ)
        C := by
  exact
    (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp
      (remark_7_5_lifted_cover_inequality_is_facet_defining
        weights capacity C μ h lam hctx hinterval hupper)).2

/-- Remark 7.5 (3). Under the strengthened upper bound
`a_j ≤ μ_{h(j)+1} - λ` for all `j ∉ C`, any facet-defining lifting of the minimal cover
inequality associated with `C` coincides with the coefficient vector from Remark 7.5. -/
theorem remark_7_5_eq_of_mem_facet_defining_liftings
    (weights : Fin n → ℕ)
    (capacity : ℕ)
    (C : Finset (Fin n))
    (μ : ℕ → ℕ)
    (h : Fin n → ℕ)
    (lam : ℕ)
    (hctx : remark_7_5_theorem_7_4_context weights capacity C μ lam)
    (hinterval : remark_7_5_interval_indices weights C μ h)
    (hupper : remark_7_5_strong_upper_bound weights C μ h lam)
    {α : Fin n → ℝ}
    (hα : α ∈ facet_defining_liftings_of_minimal_cover_inequality weights capacity C) :
    α = remark_7_5_lifting_coeff C h := by
  ext j
  by_cases hj : j ∈ C
  · have hvalid :
        α ∈ valid_liftings_of_minimal_cover_inequality weights capacity C :=
      (mem_facet_defining_liftings_of_minimal_cover_inequality_iff.mp hα).1
    -- On the cover, every valid lifting matches the Remark 7.5 coefficient vector.
    simpa using eqOnCoverOfMemValidLiftings weights capacity C h hvalid hj
  · -- Off the cover, the strengthened upper bound should force the exact Remark 7.5 coefficient.
    simpa [remark_7_5_lifting_coeff_apply_of_not_mem hj] using
      remark_7_5_offCoverEqOfMemFacetDefining
        weights capacity C μ h lam hctx hinterval hupper hα hj

end Remark75

#print axioms remark_7_5_lifted_cover_inequality_is_lifting
#print axioms remark_7_5_lifted_cover_inequality_is_facet_defining
#print axioms remark_7_5_eq_of_mem_facet_defining_liftings
