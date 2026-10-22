/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

variable {ι : Type*} [Fintype ι]

/-- The textbook finite-index function `d_φ`, given by the sum `∑ i, y i * φ (x i / y i)` when all
coordinates of `y` are positive and by `+∞` otherwise. Specializing `ι` to `Fin N` recovers the
usual coordinate model of `ℝ^N × ℝ^N`. -/
noncomputable def coordinatePerspectiveSum (ι : Type*) [Fintype ι] (φ : ℝ → EReal) :
    ((ι → ℝ) × (ι → ℝ)) → EReal :=
  fun p ↦
    if ∀ i, 0 < p.2 i then
      ∑ i, (p.2 i : EReal) * φ (p.1 i / p.2 i)
    else
      ⊤

-- Proof sketch: unfold `coordinatePerspectiveSum` and simplify the positive branch of the defining
-- `if` using the hypothesis that every coordinate of `y` is positive.
/-- If every coordinate of `y` is positive, then `coordinatePerspectiveSum ι φ (x, y)` is the
finite sum `∑ i, y i * φ (x i / y i)`. -/
theorem coordinatePerspectiveSum_apply_of_pos (ι : Type*) [Fintype ι] (φ : ℝ → EReal)
    (x y : ι → ℝ)
    (hy : ∀ i, 0 < y i) :
    coordinatePerspectiveSum ι φ (x, y) = ∑ i, (y i : EReal) * φ (x i / y i) := by
  -- Unfold the definition and select the positive branch using the coordinatewise positivity
  -- assumption on `y`.
  simp [coordinatePerspectiveSum, hy]

/-- Helper for Example 8.26: every swapped scalar perspective value stays above `⊥` when `φ`
never attains `⊥`. -/
private theorem swapped_perspective_ne_bot (φ : ℝ → EReal) (hφ_noBot : ∀ t, φ t ≠ ⊥)
    (p : ℝ × ℝ) :
    perspective φ (p.2, p.1) ≠ ⊥ := by
  by_cases hp : 0 < p.2
  · -- On the positive branch, a nonnegative real factor times a non-`⊥` value is still non-`⊥`.
    rw [perspective_apply_of_pos φ hp, EReal.mul_ne_bot]
    refine ⟨Or.inl (EReal.coe_ne_bot p.2), Or.inr (hφ_noBot _), Or.inl (EReal.coe_ne_top p.2),
      Or.inl (EReal.coe_nonneg.mpr hp.le)⟩
  · have hp_nonpos : p.2 ≤ 0 := le_of_not_gt hp
    -- On the nonpositive branch, the perspective is `⊤`, hence certainly not `⊥`.
    rw [perspective_apply_of_nonpos φ hp_nonpos]
    simp

omit [Fintype ι] in
/-- Helper for Example 8.26: a finite `EReal` sum avoids `⊥` when each summand does. -/
private lemma finset_sum_ne_bot_of_forall_ne_bot_local {s : Finset ι} {a : ι → EReal}
    (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊥ := by
  classical
  -- Induct over the finite set and use the two-term characterization of `EReal` sums avoiding
  -- `⊥`.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    rw [Finset.sum_insert his, EReal.add_ne_bot_iff]
    constructor
    · exact hbot i (Finset.mem_insert_self i s)
    · exact ih (fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj))

omit [Fintype ι] in
/-- Helper for Example 8.26: under a coordinatewise non-`⊥` hypothesis, a finite `EReal` sum is
different from `⊤` exactly when each summand is. -/
private lemma finset_sum_ne_top_iff_of_forall_ne_bot_local {s : Finset ι} {a : ι → EReal}
    (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊤ ↔ ∀ i ∈ s, a i ≠ ⊤ := by
  classical
  -- Induct over the finite set and reduce to the two-term `EReal` criterion.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    have hbot_i : a i ≠ ⊥ := hbot i (Finset.mem_insert_self i s)
    have hbot_s : ∀ j ∈ s, a j ≠ ⊥ := fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj)
    have hsum_s_ne_bot : s.sum a ≠ ⊥ := finset_sum_ne_bot_of_forall_ne_bot_local hbot_s
    rw [Finset.sum_insert his, EReal.add_ne_top_iff_ne_top₂ hbot_i hsum_s_ne_bot, ih hbot_s]
    constructor
    · intro h j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact h.1
      · exact h.2 j hj'
    · intro h
      constructor
      · exact h i (Finset.mem_insert_self i s)
      · intro j hj
        exact h j (Finset.mem_insert_of_mem hj)

omit [Fintype ι] in
/-- Helper for Example 8.26: a nonnegative finite `EReal` scalar distributes across a finite sum.
-/
private lemma mul_finset_sum_of_nonneg_of_ne_top_local
    (a : EReal) (ha_nonneg : 0 ≤ a) (ha_ne_top : a ≠ ⊤) (s : Finset ι) (b : ι → EReal) :
    a * s.sum b = s.sum (fun i ↦ a * b i) := by
  classical
  -- This is the finite-sum induction form of `EReal.left_distrib_of_nonneg_of_ne_top`.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his,
      EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top, ih]

/-- Helper for Example 8.26: the coordinate divergence is exactly the finite sum of the swapped
scalar perspective terms. -/
private theorem coordinatePerspectiveSum_eq_sum_perspective (ι : Type*) [Fintype ι] (φ : ℝ → EReal)
    (hφ_noBot : ∀ t, φ t ≠ ⊥) (x y : ι → ℝ) :
    coordinatePerspectiveSum ι φ (x, y) = ∑ i, perspective φ (y i, x i) := by
  by_cases hypos : ∀ i, 0 < y i
  · -- On the positive orthant, both definitions reduce to the same explicit weighted sum.
    rw [coordinatePerspectiveSum_apply_of_pos ι φ x y hypos]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [perspective_apply_of_pos φ (hypos i)]
    -- The scalar perspective argument is `x i / y i` after identifying real scalar multiplication
    -- with multiplication.
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  · have hnotpos := hypos
    push Not at hnotpos
    rcases hnotpos with ⟨i, hyi⟩
    -- Outside the positive orthant, the definition gives `⊤`; one coordinate perspective term is
    -- already `⊤`, so the finite sum is `⊤` as well.
    rw [coordinatePerspectiveSum, if_neg]
    · symm
      by_contra hsum_ne_top
      have hcoord_ne_top :
          ∀ j ∈ (Finset.univ : Finset ι), perspective φ (y j, x j) ≠ ⊤ := by
        exact
          (finset_sum_ne_top_iff_of_forall_ne_bot_local
            (s := (Finset.univ : Finset ι)) (a := fun j ↦ perspective φ (y j, x j))
            (fun j _ ↦ swapped_perspective_ne_bot φ hφ_noBot (x j, y j))).1 hsum_ne_top
      have hterm_top : perspective φ (y i, x i) = ⊤ := by
        rw [perspective_apply_of_nonpos φ hyi]
      exact (hcoord_ne_top i (by simp)) hterm_top
    · simpa using hypos

/-- Helper for Example 8.26: swapping the two scalar coordinates preserves convexity of the
perspective epigraph. -/
private theorem convex_epigraph_swapped_perspective (φ : ℝ → EReal)
    (hφ_convex : Convex ℝ {p : ℝ × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ (epigraph (fun p : ℝ × ℝ ↦ perspective φ (p.2, p.1))) := by
  have hperspective_convex : Convex ℝ (epigraph (perspective φ)) := by
    -- Proposition 8.25 applies once the scalar hypothesis is rewritten as `Convex ℝ (epigraph φ)`.
    exact convex_epigraph_perspective φ (by simpa [epigraph] using hφ_convex)
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨⟨ξ₁, η₁⟩, t₁⟩
  rcases q with ⟨⟨ξ₂, η₂⟩, t₂⟩
  have hp' : ((η₁, ξ₁), t₁) ∈ epigraph (perspective φ) := by
    -- Reorder the scalar coordinates to fit the perspective epigraph from Proposition 8.25.
    simpa [mem_epigraph_iff] using hp
  have hq' : ((η₂, ξ₂), t₂) ∈ epigraph (perspective φ) := by
    -- The second endpoint is handled by the same swap.
    simpa [mem_epigraph_iff] using hq
  have hcombo' :
      a • ((η₁, ξ₁), t₁) + b • ((η₂, ξ₂), t₂) ∈ epigraph (perspective φ) := by
    -- Convexity of the unswapped perspective epigraph controls the swapped convex combination.
    exact (convex_iff_forall_pos.mp hperspective_convex) hp' hq' ha hb hab
  -- Reorder the scalar coordinates back to the function used in Example 8.26.
  simpa [mem_epigraph_iff, Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc] using hcombo'

/-- Helper for Example 8.26: domain membership of the full coordinate sum forces domain membership
for every scalar swapped perspective term. -/
private theorem mem_dom_swapped_perspective_of_mem_dom_coordinatePerspectiveSum (ι : Type*)
    [Fintype ι] (φ : ℝ → EReal) (hφ_noBot : ∀ t, φ t ≠ ⊥) {x y : ι → ℝ}
    (hxy : (x, y) ∈ dom (coordinatePerspectiveSum ι φ)) :
    ∀ i, (x i, y i) ∈ dom (fun p : ℝ × ℝ ↦ perspective φ (p.2, p.1)) := by
  have hsum_ne_top : (∑ i, perspective φ (y i, x i)) ≠ ⊤ := by
    -- Rewrite the global domain membership into finiteness of the scalar perspective sum.
    rw [mem_dom_iff] at hxy
    simpa [coordinatePerspectiveSum_eq_sum_perspective ι φ hφ_noBot x y] using ne_of_lt hxy
  have hcoord_ne_top :
      ∀ j ∈ (Finset.univ : Finset ι), perspective φ (y j, x j) ≠ ⊤ := by
    exact
      (finset_sum_ne_top_iff_of_forall_ne_bot_local
        (s := (Finset.univ : Finset ι)) (a := fun j ↦ perspective φ (y j, x j))
        (fun j _ ↦ swapped_perspective_ne_bot φ hφ_noBot (x j, y j))).1 hsum_ne_top
  intro i
  -- Domain membership is exactly the statement that the scalar perspective value is different from
  -- `⊤`.
  rw [mem_dom_iff]
  exact lt_top_iff_ne_top.mpr (hcoord_ne_top i (by simp))

-- Proof sketch: view the real-height epigraph of `φ` as convex by hypothesis, identify each
-- coordinate contribution with the scalar perspective construction from Example 8.26, and then use
-- finite-sum stability of convex epigraphs over the index type `ι`.
/-- Example 8.26: if `φ : ℝ → ]-∞,+∞]` is convex, then the function on a finite family
`(ι → ℝ) × (ι → ℝ)` defined by
`(x, y) ↦ ∑ i, y i * φ (x i / y i)` on the positive orthant and to `+∞` otherwise has convex
real-height epigraph. -/
theorem convex_coordinatePerspectiveSum (ι : Type*) [Fintype ι] (φ : ℝ → EReal)
    (hφ_noBot : ∀ t, φ t ≠ ⊥)
    (hφ_convex : Convex ℝ {p : ℝ × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ {p : (((ι → ℝ) × (ι → ℝ)) × ℝ) |
      coordinatePerspectiveSum ι φ p.1 ≤ (p.2 : EReal)} := by
  -- The no-bottom hypothesis is the formal counterpart of the textbook codomain `]-∞,+∞]`.
  -- Route correction: rather than hiding the finite-dimensional structure inside `lp`, we rewrite
  -- the target as a finite sum of scalar perspectives and sum the coordinatewise Jensen
  -- inequalities.
  change Convex ℝ (epigraph (coordinatePerspectiveSum ι φ))
  refine (convex_epigraph_iff_jensen_on_dom (coordinatePerspectiveSum ι φ)).2 ?_
  intro p q hp hq α hα hα_lt_one
  rcases p with ⟨x₁, y₁⟩
  rcases q with ⟨x₂, y₂⟩
  let αE : EReal := α
  let βE : EReal := (1 - α : ℝ)
  have hαE_nonneg : 0 ≤ αE := by
    exact EReal.coe_nonneg.mpr hα.le
  have hβE_nonneg : 0 ≤ βE := by
    exact EReal.coe_nonneg.mpr (sub_nonneg.mpr (le_of_lt hα_lt_one))
  have hαE_ne_top : αE ≠ ⊤ := EReal.coe_ne_top α
  have hβE_ne_top : βE ≠ ⊤ := EReal.coe_ne_top (1 - α)
  have hscalar_jensen :
      ∀ {u v : ℝ × ℝ},
        u ∈ dom (fun z : ℝ × ℝ ↦ perspective φ (z.2, z.1)) →
        v ∈ dom (fun z : ℝ × ℝ ↦ perspective φ (z.2, z.1)) →
        perspective φ ((α • u + (1 - α) • v).2, (α • u + (1 - α) • v).1) ≤
          αE * perspective φ (u.2, u.1) + βE * perspective φ (v.2, v.1) := by
    intro u v hu hv
    -- Proposition 8.4 turns scalar convexity of the swapped perspective epigraph into Jensen's
    -- inequality on its domain.
    simpa [αE, βE] using
      ((convex_epigraph_iff_jensen_on_dom (fun z : ℝ × ℝ ↦ perspective φ (z.2, z.1))).1
        (convex_epigraph_swapped_perspective φ hφ_convex) hu hv hα hα_lt_one)
  have hpcoord :
      ∀ i, (x₁ i, y₁ i) ∈ dom (fun z : ℝ × ℝ ↦ perspective φ (z.2, z.1)) :=
    mem_dom_swapped_perspective_of_mem_dom_coordinatePerspectiveSum ι φ hφ_noBot hp
  have hqcoord :
      ∀ i, (x₂ i, y₂ i) ∈ dom (fun z : ℝ × ℝ ↦ perspective φ (z.2, z.1)) :=
    mem_dom_swapped_perspective_of_mem_dom_coordinatePerspectiveSum ι φ hφ_noBot hq
  have hpointwise :
      ∀ i,
        perspective φ
            (((α • y₁ + (1 - α) • y₂) i), ((α • x₁ + (1 - α) • x₂) i)) ≤
          αE * perspective φ (y₁ i, x₁ i) + βE * perspective φ (y₂ i, x₂ i) := by
    intro i
    -- Apply the scalar Jensen inequality at the `i`th coordinate pair.
    simpa [αE, βE, Pi.smul_apply, Pi.add_apply, Prod.smul_mk, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hscalar_jensen (hpcoord i) (hqcoord i)
  calc
    coordinatePerspectiveSum ι φ (α • (x₁, y₁) + (1 - α) • (x₂, y₂))
        = ∑ i,
            perspective φ
              (((α • y₁ + (1 - α) • y₂) i), ((α • x₁ + (1 - α) • x₂) i)) := by
            -- Rewrite the coordinate divergence of the convex combination as a finite sum of
            -- scalar perspectives.
            simpa [Prod.smul_mk] using
              coordinatePerspectiveSum_eq_sum_perspective ι φ hφ_noBot
                (α • x₁ + (1 - α) • x₂) (α • y₁ + (1 - α) • y₂)
    _ ≤ ∑ i, (αE * perspective φ (y₁ i, x₁ i) + βE * perspective φ (y₂ i, x₂ i)) := by
          -- Sum the coordinatewise Jensen inequalities over the finite index set.
          exact Finset.sum_le_sum fun i _ ↦ hpointwise i
    _ = ∑ i, αE * perspective φ (y₁ i, x₁ i) +
          ∑ i, βE * perspective φ (y₂ i, x₂ i) := by
            rw [Finset.sum_add_distrib]
    _ = αE * ∑ i, perspective φ (y₁ i, x₁ i) +
          βE * ∑ i, perspective φ (y₂ i, x₂ i) := by
            -- Pull the two nonnegative coefficients through the finite sums.
            have hxsum :
                ∑ i, αE * perspective φ (y₁ i, x₁ i) =
                  αE * ∑ i, perspective φ (y₁ i, x₁ i) := by
              symm
              exact mul_finset_sum_of_nonneg_of_ne_top_local αE hαE_nonneg hαE_ne_top Finset.univ
                (fun i ↦ perspective φ (y₁ i, x₁ i))
            have hysum :
                ∑ i, βE * perspective φ (y₂ i, x₂ i) =
                  βE * ∑ i, perspective φ (y₂ i, x₂ i) := by
              symm
              exact mul_finset_sum_of_nonneg_of_ne_top_local βE hβE_nonneg hβE_ne_top Finset.univ
                (fun i ↦ perspective φ (y₂ i, x₂ i))
            rw [hxsum, hysum]
    _ = (α : EReal) * coordinatePerspectiveSum ι φ (x₁, y₁) +
          (((1 - α : ℝ) : EReal) * coordinatePerspectiveSum ι φ (x₂, y₂)) := by
            -- Rewrite the two endpoint scalar sums back into the original coordinate divergence.
            rw [← coordinatePerspectiveSum_eq_sum_perspective ι φ hφ_noBot x₁ y₁,
              ← coordinatePerspectiveSum_eq_sum_perspective ι φ hφ_noBot x₂ y₂]

end ERealFunction
