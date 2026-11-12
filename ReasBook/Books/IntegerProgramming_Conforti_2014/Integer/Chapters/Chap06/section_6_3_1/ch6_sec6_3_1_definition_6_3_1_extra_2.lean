/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1

section Definition631Extra2

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "IntAssignment" => Rq →₀ ℤ

/-- Definition 6.3.1-extra-2 (1): a valid function `π` for `G_f` is extreme when it cannot be
written as the midpoint of two valid functions unless both of them coincide with `π`. -/
class pure_integer_extreme_valid_function (f : Rq) (π : Rq → ℝ) :
    Prop extends pure_integer_valid_function f π where
  /-- If `π` is the average of two valid functions, then both of those valid functions are equal
  to `π`. -/
  eq_of_eq_midpoint {π₁ π₂ : Rq → ℝ}
      (hπ₁ : pure_integer_valid_function f π₁)
      (hπ₂ : pure_integer_valid_function f π₂)
      (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
      π = π₁ ∧ π = π₂

/-- The ambient set of valid functions for `G_f`. -/
def pure_integer_valid_functions (f : Rq) : Set (Rq → ℝ) :=
  {π | pure_integer_valid_function f π}

/-- Unfolding lemma for `pure_integer_valid_functions`. -/
theorem mem_pure_integer_valid_functions_iff {f : Rq} {π : Rq → ℝ} :
    π ∈ pure_integer_valid_functions f ↔ pure_integer_valid_function f π :=
  Iff.rfl

/-- Helper for Definition 6.3.1-extra-2: the cut sum of a convex combination of valid-function
coefficients is the same convex combination of the corresponding cut sums. -/
theorem pure_integer_sum_combo
    {a b : ℝ} {π₁ π₂ : Rq → ℝ} {x : IntAssignment} :
    x.sum (fun r n ↦ (n : ℝ) * ((a • π₁ + b • π₂) r)) =
      a * x.sum (fun r n ↦ (n : ℝ) * π₁ r) +
        b * x.sum (fun r n ↦ (n : ℝ) * π₂ r) := by
  classical
  -- Expand the pointwise convex combination and factor the finite sum coefficientwise.
  simp_rw [Finsupp.sum, Pi.add_apply, Pi.smul_apply, mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro r hr
    ring
  · refine Finset.sum_congr rfl ?_
    intro r hr
    ring

/-- Helper for Definition 6.3.1-extra-2: if a feasible assignment has nonnegative coefficients,
then its cut sum is monotone under pointwise domination of coefficient functions. -/
theorem pure_integer_sum_le_of_le
    {x : IntAssignment} {π₁ π₂ : Rq → ℝ}
    (hx : ∀ r, 0 ≤ x r) (hπ : ∀ r, π₁ r ≤ π₂ r) :
    x.sum (fun r n ↦ (n : ℝ) * π₁ r) ≤ x.sum (fun r n ↦ (n : ℝ) * π₂ r) := by
  -- Compare the two finite sums termwise using the nonnegativity of the feasible coefficients.
  refine Finsupp.sum_le_sum ?_
  intro r hr
  exact mul_le_mul_of_nonneg_left (hπ r) (show 0 ≤ (x r : ℝ) by exact_mod_cast hx r)

/-- Helper for Definition 6.3.1-extra-2: the owner set of pure-integer valid functions is convex.
-/
theorem pure_integer_valid_functions_convex {f : Rq} :
    Convex ℝ (pure_integer_valid_functions f) := by
  rw [convex_iff_add_mem]
  intro π₁ hπ₁ π₂ hπ₂ a b ha hb hab
  rw [mem_pure_integer_valid_functions_iff] at hπ₁ hπ₂ ⊢
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Pointwise nonnegativity is preserved by nonnegative convex coefficients.
    intro r
    exact add_nonneg (smul_nonneg ha (hπ₁.nonneg r)) (smul_nonneg hb (hπ₂.nonneg r))
  · -- The defining inequality is linear in the coefficient function.
    intro x hx
    have h₁ : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π₁ r) :=
      pure_integer_valid_function_one_le_sum hπ₁ hx
    have h₂ : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π₂ r) :=
      pure_integer_valid_function_one_le_sum hπ₂ hx
    rw [pure_integer_sum_combo]
    nlinarith [h₁, h₂, ha, hb, hab]

/-- Helper for Definition 6.3.1-extra-2: midpoint extremality already rules out every open-segment
decomposition inside the owner set of valid functions. -/
theorem pure_integer_extreme_eq_of_mem_openSegment
    {f : Rq} {π π₁ π₂ : Rq → ℝ}
    (hπ : pure_integer_extreme_valid_function f π)
    (hπ₁ : pure_integer_valid_function f π₁)
    (hπ₂ : pure_integer_valid_function f π₂)
    (hseg : π ∈ openSegment ℝ π₁ π₂) :
    π₁ = π ∧ π₂ = π := by
  have hconv := pure_integer_valid_functions_convex (f := f)
  have hπ₁_mem : π₁ ∈ pure_integer_valid_functions f := hπ₁
  have hπ₂_mem : π₂ ∈ pure_integer_valid_functions f := hπ₂
  rcases mem_openSegment_iff_div.mp hseg with ⟨a, b, ha, hb, hrepr⟩
  let α : ℝ := a / (a + b)
  let β : ℝ := b / (a + b)
  have hab : 0 < a + b := add_pos ha hb
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hβpos : 0 < β := by
    dsimp [β]
    positivity
  have hα : 0 ≤ α := le_of_lt hαpos
  have hβ : 0 ≤ β := le_of_lt hβpos
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    rw [← add_div, div_self hab.ne']
  have hrepr' : α • π₁ + β • π₂ = π := by
    simpa [α, β] using hrepr
  have hhalf : (1 / 2 : ℝ) ≤ α ∨ (1 / 2 : ℝ) ≤ β := by
    by_cases hαhalf : (1 / 2 : ℝ) ≤ α
    · exact Or.inl hαhalf
    · right
      linarith
  rcases hhalf with hαhalf | hβhalf
  · let ρ : Rq → ℝ := (2 * α - 1) • π₁ + (2 * β) • π₂
    have hρ_mem : ρ ∈ pure_integer_valid_functions f := by
      -- Keep the same owner set by expressing the auxiliary endpoint as another convex
      -- combination of the original valid endpoints.
      refine hconv hπ₁_mem hπ₂_mem ?_ ?_ ?_
      · linarith
      · positivity
      · linarith
    have hρ : pure_integer_valid_function f ρ := by
      rwa [mem_pure_integer_valid_functions_iff] at hρ_mem
    have hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • ρ := by
      -- Rewrite the open-segment representation into a midpoint representation.
      ext r
      have hrepr_r := congrArg (fun φ : Rq → ℝ => φ r) hrepr'
      dsimp [ρ] at *
      nlinarith
    have hleft : π = π₁ := (hπ.eq_of_eq_midpoint hπ₁ hρ hmid).1
    have hright : π₂ = π := by
      -- Once the left endpoint collapses to `π`, the open segment can only contain `π` if the
      -- right endpoint also collapses.
      have : π ∈ openSegment ℝ π π₂ := by simpa [hleft] using hseg
      exact (left_mem_openSegment_iff.mp this).symm
    exact ⟨hleft.symm, hright⟩
  · let ρ : Rq → ℝ := (2 * α) • π₁ + (2 * β - 1) • π₂
    have hρ_mem : ρ ∈ pure_integer_valid_functions f := by
      -- In the complementary case, use `π₂` as the midpoint endpoint and absorb the excess
      -- weight into the first endpoint.
      refine hconv hπ₁_mem hπ₂_mem ?_ ?_ ?_
      · positivity
      · linarith
      · linarith
    have hρ : pure_integer_valid_function f ρ := by
      rwa [mem_pure_integer_valid_functions_iff] at hρ_mem
    have hmid : π = (1 / 2 : ℝ) • ρ + (1 / 2 : ℝ) • π₂ := by
      -- Rewrite the same open-segment representation as a midpoint with right endpoint `π₂`.
      ext r
      have hrepr_r := congrArg (fun φ : Rq → ℝ => φ r) hrepr'
      dsimp [ρ] at *
      nlinarith
    have hright : π = π₂ := (hπ.eq_of_eq_midpoint hρ hπ₂ hmid).2
    have hleft : π₁ = π := by
      -- Once the right endpoint collapses to `π`, the left endpoint must also collapse.
      have : π ∈ openSegment ℝ π₁ π := by simpa [hright] using hseg
      exact right_mem_openSegment_iff.mp this
    exact ⟨hleft, hright.symm⟩

/-- The source-facing midpoint notion of extremality for valid functions bridges to the canonical
owner `Set.extremePoints ℝ` on the ambient set of valid functions. -/
theorem pure_integer_extreme_valid_function_iff_mem_extremePoints
    {f : Rq} {π : Rq → ℝ} :
    pure_integer_extreme_valid_function f π ↔
      π ∈ (pure_integer_valid_functions f).extremePoints ℝ := by
  constructor
  · intro hπ
    rw [mem_extremePoints_iff_left]
    constructor
    · exact mem_pure_integer_valid_functions_iff.mpr
        { nonneg := hπ.nonneg
          one_le_sum := hπ.one_le_sum }
    · -- Reduce an arbitrary open-segment decomposition to the midpoint case built into the
      -- definition of extremality.
      intro π₁ hπ₁ π₂ hπ₂ hseg
      exact (pure_integer_extreme_eq_of_mem_openSegment hπ hπ₁ hπ₂ hseg).1
  · intro hπ
    rw [mem_extremePoints_iff_left] at hπ
    have hvalid : pure_integer_valid_function f π := by
      exact hπ.1
    refine
      { nonneg := hvalid.nonneg
        one_le_sum := hvalid.one_le_sum
        eq_of_eq_midpoint := ?_ }
    intro π₁ π₂ hπ₁ hπ₂ hmid
    -- A midpoint identity produces open-segment membership, so the extreme-point owner property
    -- collapses both midpoint endpoints to `π`.
    have hseg : π ∈ openSegment ℝ π₁ π₂ := by
      have hmidpoint : midpoint ℝ π₁ π₂ = π := by
        calc
          midpoint ℝ π₁ π₂ = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂ := by
            rw [midpoint_eq_smul_add, smul_add]
            norm_num
          _ = π := hmid.symm
      simpa [hmidpoint] using midpoint_mem_openSegment (𝕜 := ℝ) π₁ π₂
    have hleft : π₁ = π := hπ.2 π₁ (mem_pure_integer_valid_functions_iff.mpr hπ₁)
        π₂ (mem_pure_integer_valid_functions_iff.mpr hπ₂) hseg
    have hright : π₂ = π := by
      have : π ∈ openSegment ℝ π π₂ := by simpa [hleft] using hseg
      exact (left_mem_openSegment_iff.mp this).symm
    exact ⟨hleft.symm, hright.symm⟩

/-- Definition 6.3.1-extra-2 (2): if `π = (π₁ + π₂) / 2`, then the cut inequality defined by `π`
is implied by the two cut inequalities defined by `π₁` and `π₂`. -/
theorem pure_integer_one_le_sum_of_eq_midpoint
    {π π₁ π₂ : Rq → ℝ}
    (hπ : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    {x : IntAssignment}
    (h₁ : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π₁ r))
    (h₂ : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π₂ r)) :
    1 ≤ x.sum (fun r n ↦ (n : ℝ) * π r) := by
  -- Rewrite the target cut sum as the midpoint of the two premise cut sums.
  rw [hπ, pure_integer_sum_combo]
  linarith

/-- Helper for Definition 6.3.1-extra-2: reflecting a valid function `π' ≤ π` across `π`
produces another valid function. -/
theorem pure_integer_reflected_valid_function_of_le
    {f : Rq} {π π' : Rq → ℝ}
    (hπ : pure_integer_valid_function f π)
    (hπ' : pure_integer_valid_function f π')
    (hle : ∀ r, π' r ≤ π r) :
    pure_integer_valid_function f (fun r ↦ (2 : ℝ) * π r - π' r) := by
  have hπ'nonneg : ∀ r, 0 ≤ π' r := hπ'.nonneg
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Pointwise reflection preserves nonnegativity because `π'` sits below `π`.
    intro r
    linarith [hπ.nonneg r, hπ'nonneg r, hle r]
  · -- For feasible assignments, the reflected cut sum is `2 * sum π - sum π'`, and the second
    -- sum is bounded above by the first one because all assignment coefficients are nonnegative.
    intro x hx
    rw [show x.sum (fun r n ↦ (n : ℝ) * ((fun r ↦ (2 : ℝ) * π r - π' r) r)) =
        x.sum (fun r n ↦ (n : ℝ) * ((2 : ℝ) • π + (-1 : ℝ) • π') r) by
          simp [Pi.smul_apply, sub_eq_add_neg, mul_comm]]
    rw [pure_integer_sum_combo]
    have hx' : pure_integer_feasible_point f x := hx
    have hπ_sum : 1 ≤ x.sum (fun r n ↦ (n : ℝ) * π r) :=
      pure_integer_valid_function_one_le_sum hπ hx
    have hπ'_sum : x.sum (fun r n ↦ (n : ℝ) * π' r) ≤ x.sum (fun r n ↦ (n : ℝ) * π r) :=
      pure_integer_sum_le_of_le hx'.nonneg hle
    linarith

/-- Definition 6.3.1-extra-2 (3): every extreme valid function for `G_f` is minimal. -/
theorem pure_integer_extreme_valid_function.isMinimal
    {f : Rq} {π : Rq → ℝ}
    (hπ : pure_integer_extreme_valid_function f π) :
    pure_integer_minimal_valid_function f π := by
  have hπvalid : pure_integer_valid_function f π :=
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum }
  refine
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum
      eq_of_le := ?_ }
  intro π' hπ' hle
  let ρ : Rq → ℝ := fun r ↦ (2 : ℝ) * π r - π' r
  have hρ : pure_integer_valid_function f ρ :=
    pure_integer_reflected_valid_function_of_le hπvalid hπ' hle
  have hmid : π = (1 / 2 : ℝ) • π' + (1 / 2 : ℝ) • ρ := by
    -- Route correction: prove minimality through the source reflection argument
    -- `π = (π' + (2π - π')) / 2`, not through an unrelated owner-level criterion.
    ext r
    dsimp [ρ]
    ring
  -- Extremality forces the reflected partner and the dominated valid function to coincide with `π`.
  exact (hπ.eq_of_eq_midpoint hπ' hρ hmid).1.symm

end Definition631Extra2
