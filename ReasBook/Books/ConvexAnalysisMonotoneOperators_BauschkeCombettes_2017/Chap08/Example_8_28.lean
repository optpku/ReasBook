/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

/-- The scalar kernel `t ↦ (t - 1) log t` on the positive half-line, extended by `+∞` on
`(-∞, 0]`. -/
noncomputable def logarithmicDifferenceKernel : ℝ → EReal :=
  fun t ↦ if 0 < t then (((t - 1) * Real.log t : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `logarithmicDifferenceKernel` and simplify the defining `if` using the
-- positivity hypothesis on `t`.
/-- On the positive half-line, `logarithmicDifferenceKernel` is exactly `(t - 1) log t`. -/
theorem logarithmicDifferenceKernel_apply_of_pos {t : ℝ} (ht : 0 < t) :
    logarithmicDifferenceKernel t = (((t - 1) * Real.log t : ℝ) : EReal) := by
  -- On `Ioi 0`, the extended-valued definition reduces to its real branch.
  simp [logarithmicDifferenceKernel, ht]

/-- Helper for Example 8.28: real-height epigraph membership for the scalar logarithmic-difference
kernel is exactly strict positivity together with the corresponding real inequality. -/
private lemma mem_epigraph_logarithmicDifferenceKernel_iff {t r : ℝ} :
    (t, r) ∈ epigraph logarithmicDifferenceKernel ↔
      0 < t ∧ (t - 1) * Real.log t ≤ r := by
  constructor
  · intro h
    rw [mem_epigraph_iff] at h
    by_cases ht : 0 < t
    · constructor
      · exact ht
      · have h' : (((t - 1) * Real.log t : ℝ) : EReal) ≤ (r : EReal) := by
          -- The positive branch identifies the extended-real inequality with a real one.
          simpa [logarithmicDifferenceKernel, ht] using h
        exact_mod_cast h'
    · have htop := h
      -- Outside `Ioi 0`, the kernel is `⊤`, so no real epigraph ordinate can dominate it.
      simp [logarithmicDifferenceKernel, ht] at htop
  · rintro ⟨ht, htr⟩
    rw [mem_epigraph_iff]
    have h' : (((t - 1) * Real.log t : ℝ) : EReal) ≤ (r : EReal) := by
      -- Cast the real bound into `EReal` before returning to the positive branch.
      exact_mod_cast htr
    simpa [logarithmicDifferenceKernel, ht] using h'

/-- Helper for Example 8.28: the scalar logarithmic-difference kernel never takes the value
`-∞`. -/
private theorem logarithmicDifferenceKernel_ne_bot (t : ℝ) :
    logarithmicDifferenceKernel t ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- On the positive branch the value is a real number, hence not `-∞`.
    rw [logarithmicDifferenceKernel_apply_of_pos ht]
    exact EReal.coe_ne_bot _
  · -- On the nonpositive branch the value is `⊤`.
    simp [logarithmicDifferenceKernel, ht]

/-- Helper for Example 8.28: multiplying the scalar kernel by a positive real weight still avoids
`-∞`. -/
private theorem scaled_logarithmicDifferenceKernel_ne_bot {y t : ℝ} (hy : 0 < y) :
    (y : EReal) * logarithmicDifferenceKernel t ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- In the positive branch the weighted value is still represented by a real number.
    rw [logarithmicDifferenceKernel_apply_of_pos ht, EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · -- In the nonpositive branch the kernel is `⊤`, and a positive finite weight preserves `⊤`.
    rw [logarithmicDifferenceKernel, if_neg ht, EReal.coe_mul_top_of_pos hy]
    simp

/-- Helper for Example 8.28: a finite `EReal` sum avoids `⊥` when each summand does. -/
private lemma finset_sum_ne_bot_of_forall_ne_bot_local {ι : Type*} {s : Finset ι}
    {a : ι → EReal} (hbot : ∀ i ∈ s, a i ≠ ⊥) :
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

/-- Helper for Example 8.28: under a coordinatewise non-`⊥` hypothesis, a finite `EReal` sum is
different from `⊤` exactly when each summand is. -/
private lemma finset_sum_ne_top_iff_of_forall_ne_bot_local {ι : Type*} {s : Finset ι}
    {a : ι → EReal} (hbot : ∀ i ∈ s, a i ≠ ⊥) :
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

/-- Helper for Example 8.28: the positive-weighted scalar kernel written in perspective form
matches the coordinate logarithmic-difference summand. -/
private lemma mul_logarithmicDifferenceKernel_div_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y * (((x / y) - 1) * Real.log (x / y)) =
      (x - y) * (Real.log x - Real.log y) := by
  have hscale : y * (x / y - 1) = x - y := by
    -- Clearing the positive denominator isolates the elementary affine factor.
    field_simp [hy.ne']
  calc
    y * (((x / y) - 1) * Real.log (x / y))
        = (y * (x / y - 1)) * Real.log (x / y) := by ring
    _ = (x - y) * Real.log (x / y) := by rw [hscale]
    _ = (x - y) * (Real.log x - Real.log y) := by
          rw [Real.log_div hx.ne' hy.ne']

-- Proof sketch: on `Ioi 0`, rewrite `(t - 1) log t` as `t log t - log t`, combine the convexity
-- of `t ↦ t log t` with the concavity of `log`, and then translate the positive-branch inequality
-- back to the extended-valued epigraph.
/-- Helper for Example 8.28: the scalar logarithmic-difference kernel has convex real-height
epigraph. -/
private theorem convex_epigraph_logarithmicDifferenceKernel :
    Convex ℝ (epigraph logarithmicDifferenceKernel) := by
  have hmul_log : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ t * Real.log t) :=
    Real.convexOn_mul_log.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
  have hkernel' : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ t * Real.log t - Real.log t) :=
    hmul_log.sub strictConcaveOn_log_Ioi.concaveOn
  have hkernel : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ (t - 1) * Real.log t) := by
    -- On the positive half-line, the textbook scalar kernel is `t log t - log t`.
    convert hkernel' using 1
    ext t
    ring_nf
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, ξ⟩
  rcases q with ⟨y, η⟩
  rw [mem_epigraph_logarithmicDifferenceKernel_iff] at hp hq
  rw [mem_epigraph_logarithmicDifferenceKernel_iff]
  constructor
  · -- Strict positivity is preserved by convex combinations with positive coefficients.
    simpa [Prod.smul_mk, smul_eq_mul] using add_pos (mul_pos ha hp.1) (mul_pos hb hq.1)
  · have hkernel_bound :
        (a * x + b * y - 1) * Real.log (a * x + b * y) ≤
          a * ((x - 1) * Real.log x) + b * ((y - 1) * Real.log y) :=
      hkernel.2 hp.1 hq.1 ha.le hb.le hab
    have hheight :
        a * ((x - 1) * Real.log x) + b * ((y - 1) * Real.log y) ≤ a * ξ + b * η := by
      -- The endpoint epigraph inequalities scale and add because the coefficients are
      -- nonnegative.
      exact add_le_add (mul_le_mul_of_nonneg_left hp.2 ha.le)
        (mul_le_mul_of_nonneg_left hq.2 hb.le)
    -- The scalar convexity bound and the endpoint heights give the epigraph inequality.
    exact le_trans hkernel_bound hheight

/-- The textbook function
`(x, y) ↦ ∑ i, (x i - y i) * (log (x i) - log (y i))`
on the positive orthant of `(Fin N → ℝ) × (Fin N → ℝ)`, extended by `+∞` elsewhere. -/
noncomputable def coordinateLogarithmicDifference (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) → EReal :=
  fun p ↦
    if ∀ i, 0 < p.1 i ∧ 0 < p.2 i then
      ∑ i, (((p.1 i - p.2 i) * (Real.log (p.1 i) - Real.log (p.2 i)) : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: unfold `coordinateLogarithmicDifference` and simplify the defining `if` using the
-- coordinatewise positivity hypotheses on `x` and `y`.
/-- If every coordinate of `x` and `y` is positive, then
`coordinateLogarithmicDifference N (x, y)` is the finite sum
`∑ i, (x i - y i) * (log (x i) - log (y i))`. -/
theorem coordinateLogarithmicDifference_apply_of_pos (N : ℕ) (x y : Fin N → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    coordinateLogarithmicDifference N (x, y) =
      ∑ i, (((x i - y i) * (Real.log (x i) - Real.log (y i)) : ℝ) : EReal) := by
  -- On the positive orthant, the extended-valued definition reduces to its explicit finite sum.
  simp [coordinateLogarithmicDifference, hx, hy]

-- Proof sketch: for positive coordinates rewrite
-- `(x i - y i) * (log (x i) - log (y i)) = y i * ((x i / y i - 1) * log (x i / y i))`
-- using `Real.log_div`; if some coordinate of `y` is nonpositive both sides are `+∞`, and if some
-- coordinate of `x` is nonpositive while `y` stays positive, the corresponding scalar kernel term
-- in `coordinatePerspectiveSum` is already `+∞`.
/-- The coordinate logarithmic-difference function is the coordinate perspective sum from
Example 8.26 specialized to the scalar kernel `t ↦ (t - 1) log t` on `ℝ_{++}`. -/
theorem coordinateLogarithmicDifference_eq_coordinatePerspectiveSum (N : ℕ) :
    coordinateLogarithmicDifference N =
      coordinatePerspectiveSum (Fin N) logarithmicDifferenceKernel := by
  funext p
  rcases p with ⟨x, y⟩
  by_cases hy : ∀ i, 0 < y i
  · by_cases hx : ∀ i, 0 < x i
    · -- On the strictly positive orthant, both functions reduce to the same coordinate formula.
      rw [coordinateLogarithmicDifference_apply_of_pos N x y hx hy]
      rw [coordinatePerspectiveSum_apply_of_pos (Fin N) logarithmicDifferenceKernel x y hy]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hdiv_pos : 0 < x i / y i := div_pos (hx i) (hy i)
      rw [logarithmicDifferenceKernel_apply_of_pos hdiv_pos, EReal.coe_mul]
      -- The scalar perspective weight matches the textbook coordinate summand.
      exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
        (mul_logarithmicDifferenceKernel_div_eq (hx i) (hy i)).symm
    · have hxy : ¬ ∀ i, 0 < x i ∧ 0 < y i := by
        intro h
        exact hx (fun i ↦ (h i).1)
      push Not at hx
      rcases hx with ⟨i, hxi_nonpos⟩
      rw [coordinateLogarithmicDifference, if_neg hxy]
      rw [coordinatePerspectiveSum_apply_of_pos (Fin N) logarithmicDifferenceKernel x y hy]
      have hdiv_nonpos : x i / y i ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hxi_nonpos (hy i).le
      have hterm_top :
          (y i : EReal) * logarithmicDifferenceKernel (x i / y i) = ⊤ := by
        -- A nonpositive ratio lands in the `+∞` branch of the scalar kernel.
        rw [logarithmicDifferenceKernel, if_neg (not_lt_of_ge hdiv_nonpos)]
        exact EReal.coe_mul_top_of_pos (hy i)
      symm
      by_contra hsum_ne_top
      have hcoord_ne_top :
          ∀ j ∈ (Finset.univ : Finset (Fin N)),
            (y j : EReal) * logarithmicDifferenceKernel (x j / y j) ≠ ⊤ := by
        exact
          (finset_sum_ne_top_iff_of_forall_ne_bot_local
            (s := (Finset.univ : Finset (Fin N)))
            (a := fun j ↦ (y j : EReal) * logarithmicDifferenceKernel (x j / y j))
            (fun j _ ↦ scaled_logarithmicDifferenceKernel_ne_bot (hy j))).1 hsum_ne_top
      exact (hcoord_ne_top i (by simp)) hterm_top
  · have hxy : ¬ ∀ i, 0 < x i ∧ 0 < y i := by
      intro hxy
      exact hy (fun i ↦ (hxy i).2)
    -- If some coordinate of `y` is nonpositive, both definitions are already `+∞`.
    simp [coordinateLogarithmicDifference, coordinatePerspectiveSum, hy, hxy]

-- Proof sketch: use `coordinateLogarithmicDifference_eq_coordinatePerspectiveSum` to rewrite the
-- function into the coordinate perspective sum from Example 8.26. Then apply Example 8.26 to the
-- scalar kernel `logarithmicDifferenceKernel`, whose convexity on `ℝ` comes from
-- Proposition 8.14 (2) applied to `t ↦ (t - 1) * log t` on `Set.Ioi 0`.
/-- Example 8.28: on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`, the function equal to
`∑ i, (x i - y i) * (log (x i) - log (y i))` when every coordinate of `x` and `y` is positive and
to `+∞` otherwise is convex, expressed canonically as convexity of its epigraph. -/
theorem convex_epigraph_coordinateLogarithmicDifference (N : ℕ) :
    Convex ℝ (epigraph (coordinateLogarithmicDifference N)) := by
  have hscalar :
      Convex ℝ {p : ℝ × ℝ | logarithmicDifferenceKernel p.1 ≤ (p.2 : EReal)} := by
    -- Repackage the scalar epigraph result in the set form expected by Example 8.26.
    simpa [epigraph] using convex_epigraph_logarithmicDifferenceKernel
  let lift :
      (∀ t, logarithmicDifferenceKernel t ≠ ⊥) →
      Convex ℝ {p : ℝ × ℝ | logarithmicDifferenceKernel p.1 ≤ (p.2 : EReal)} →
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) logarithmicDifferenceKernel p.1 ≤ (p.2 : EReal)} :=
    ERealFunction.convex_coordinatePerspectiveSum (Fin N) logarithmicDifferenceKernel
  let hsum :
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) logarithmicDifferenceKernel p.1 ≤ (p.2 : EReal)} :=
    lift logarithmicDifferenceKernel_ne_bot hscalar
  -- Example 8.26 lifts the scalar epigraph convexity once the coordinate formula is identified.
  simpa [coordinateLogarithmicDifference_eq_coordinatePerspectiveSum, epigraph] using hsum

end ERealFunction
