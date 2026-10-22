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

/-- The Hellinger entropy integrand `t ↦ |√t - 1|²` on `(0, +∞)`, extended by `+∞` on
`(-∞, 0]`. -/
noncomputable def hellingerEntropy : ℝ → EReal :=
  fun t ↦
    if 0 < t then
      ((|Real.sqrt t - 1| ^ 2 : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: unfold `hellingerEntropy` and simplify the defining `if` using the hypothesis
-- `0 < t`.
/-- On positive inputs, the Hellinger entropy is `|√t - 1|²`. -/
@[simp] theorem hellingerEntropy_apply_of_pos {t : ℝ} (ht : 0 < t) :
    hellingerEntropy t = ((|Real.sqrt t - 1| ^ 2 : ℝ) : EReal) := by
  -- The positive branch of the definition is exactly the real-valued Hellinger integrand.
  simp [hellingerEntropy, ht]

-- Proof sketch: unfold `hellingerEntropy` and simplify the defining `if` using `¬ 0 < t`,
-- obtained from the hypothesis `t ≤ 0`.
/-- On nonpositive inputs, the Hellinger entropy is `+∞`. -/
@[simp] theorem hellingerEntropy_apply_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    hellingerEntropy t = ⊤ := by
  -- Outside the positive half-line, the extended-valued definition is forced to `⊤`.
  simp [hellingerEntropy, not_lt_of_ge ht]

/-- Helper for Example 8.30: real-height epigraph membership for the scalar Hellinger entropy is
equivalent to strict positivity together with the corresponding real inequality. -/
private lemma mem_epigraph_hellingerEntropy_iff {t r : ℝ} :
    (t, r) ∈ epigraph hellingerEntropy ↔ 0 < t ∧ |Real.sqrt t - 1| ^ 2 ≤ r := by
  constructor
  · intro h
    rw [mem_epigraph_iff] at h
    by_cases ht : 0 < t
    · constructor
      · exact ht
      · have h' : (((|Real.sqrt t - 1| ^ 2 : ℝ) : EReal)) ≤ (r : EReal) := by
          -- On the positive branch, the `EReal` inequality is just the cast of the real bound.
          simpa [hellingerEntropy, ht] using h
        exact_mod_cast h'
    · have htop := h
      -- If `t` is not positive, the function value is `⊤`, which no real height dominates.
      simp [hellingerEntropy, ht] at htop
  · rintro ⟨ht, htr⟩
    rw [mem_epigraph_iff]
    have h' : (((|Real.sqrt t - 1| ^ 2 : ℝ) : EReal)) ≤ (r : EReal) := by
      -- Cast the real inequality into `EReal` before returning to the positive branch.
      exact_mod_cast htr
    simpa [hellingerEntropy, ht] using h'

/-- Helper for Example 8.30: the scalar Hellinger entropy never takes the value `-∞`. -/
private theorem hellingerEntropy_ne_bot (t : ℝ) :
    hellingerEntropy t ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- On the positive branch, the value is represented by a real number.
    rw [hellingerEntropy_apply_of_pos ht]
    exact EReal.coe_ne_bot _
  · -- On the complementary branch, the value is `⊤`.
    simp [hellingerEntropy, ht]

/-- Helper for Example 8.30: multiplying the scalar Hellinger entropy by a positive real weight
still avoids `-∞`. -/
private theorem scaled_hellingerEntropy_ne_bot {y t : ℝ} (hy : 0 < y) :
    (y : EReal) * hellingerEntropy t ≠ ⊥ := by
  -- A positive finite scalar times a value in `]-∞,+∞]` cannot create `-∞`.
  rw [EReal.mul_ne_bot]
  refine ⟨Or.inl (EReal.coe_ne_bot y), Or.inr (hellingerEntropy_ne_bot t),
    Or.inl (EReal.coe_ne_top y), Or.inl (EReal.coe_nonneg.mpr hy.le)⟩

/-- Helper for Example 8.30: a finite `EReal` sum avoids `⊥` when each summand does. -/
private lemma finset_sum_ne_bot_of_forall_ne_bot_local {ι : Type*} {s : Finset ι}
    {a : ι → EReal} (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊥ := by
  classical
  -- Induct over the finite set and reduce to the two-term characterization of `EReal` sums.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    rw [Finset.sum_insert his, EReal.add_ne_bot_iff]
    constructor
    · exact hbot i (Finset.mem_insert_self i s)
    · exact ih (fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj))

/-- Helper for Example 8.30: under a coordinatewise non-`⊥` hypothesis, a finite `EReal` sum is
different from `⊤` exactly when each summand is. -/
private lemma finset_sum_ne_top_iff_of_forall_ne_bot_local {ι : Type*} {s : Finset ι}
    {a : ι → EReal} (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊤ ↔ ∀ i ∈ s, a i ≠ ⊤ := by
  classical
  -- Induct over the finite set and reduce finiteness of the sum to finiteness of each term.
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

/-- Helper for Example 8.30: coercing a finite real sum into `EReal` agrees with summing the
coerced terms. -/
private lemma ereal_coe_sum_eq_sum_coe {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) := by
  classical
  -- Expand the finite sum inductively and use the compatibility of the coercion with addition.
  let s : Finset ι := Finset.univ
  change (((s.sum fun i ↦ f i : ℝ)) : EReal) = s.sum fun i ↦ (f i : EReal)
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      norm_num

/-- Helper for Example 8.30: on the positive half-line, the real branch
`t ↦ |√t - 1|²` is convex. -/
private theorem convexOn_hellingerEntropy_branch :
    ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ |Real.sqrt t - 1| ^ 2) := by
  have hsqrt : ConcaveOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ Real.sqrt t) := by
    -- Restrict the standard concavity of `sqrt` on `[0, +∞)` to the open positive half-line.
    exact (Real.strictConcaveOn_sqrt.concaveOn).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
  have hnegsqrt : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ -Real.sqrt t) := hsqrt.neg
  have hscaled : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ (2 : ℝ) * (-Real.sqrt t)) := by
    -- Scaling a convex function by a nonnegative coefficient preserves convexity.
    exact hnegsqrt.smul (show 0 ≤ (2 : ℝ) by norm_num)
  have hid : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ t) := convexOn_id (convex_Ioi 0)
  have hsum : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ t + (2 : ℝ) * (-Real.sqrt t)) :=
    hid.add hscaled
  have hfinal : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ ↦ t + (2 : ℝ) * (-Real.sqrt t) + 1) :=
    hsum.add_const 1
  refine hfinal.congr ?_
  intro t ht
  -- On `Set.Ioi 0`, the square expands to `t - 2 * √t + 1`, which is the convex decomposition.
  change t + 2 * (-Real.sqrt t) + 1 = |Real.sqrt t - 1| ^ 2
  rw [sq_abs, sub_sq, sq]
  have hsq : Real.sqrt t * Real.sqrt t = t := by
    nlinarith [Real.sq_sqrt (show 0 ≤ t from le_of_lt ht)]
  rw [hsq]
  ring

-- Proof sketch: apply Proposition 8.14 to the real-valued branch `t ↦ |√t - 1|²` on
-- `Set.Ioi 0`, then extend by `+∞` on `(-∞, 0]` and identify the epigraph with the textbook
-- Hellinger entropy epigraph.
/-- The Hellinger entropy has convex epigraph on `ℝ × ℝ`. -/
theorem convex_epigraph_hellingerEntropy :
    Convex ℝ {p : ℝ × ℝ | hellingerEntropy p.1 ≤ (p.2 : EReal)} := by
  change Convex ℝ (epigraph hellingerEntropy)
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, ξ⟩
  rcases q with ⟨y, η⟩
  rw [mem_epigraph_hellingerEntropy_iff] at hp hq
  rw [mem_epigraph_hellingerEntropy_iff]
  constructor
  · -- Strict positivity is preserved by convex combinations with positive coefficients.
    simpa [Prod.smul_mk, smul_eq_mul] using add_pos (mul_pos ha hp.1) (mul_pos hb hq.1)
  · have hbranch :
        |Real.sqrt (a * x + b * y) - 1| ^ 2 ≤
          a * |Real.sqrt x - 1| ^ 2 + b * |Real.sqrt y - 1| ^ 2 :=
      convexOn_hellingerEntropy_branch.2 hp.1 hq.1 ha.le hb.le hab
    have hheight :
        a * |Real.sqrt x - 1| ^ 2 + b * |Real.sqrt y - 1| ^ 2 ≤ a * ξ + b * η := by
      -- The endpoint epigraph bounds scale and add because the coefficients are nonnegative.
      exact add_le_add (mul_le_mul_of_nonneg_left hp.2 ha.le)
        (mul_le_mul_of_nonneg_left hq.2 hb.le)
    -- The scalar convexity inequality and the endpoint heights yield the barycenter inequality.
    exact le_trans hbranch hheight

/-- The Hellinger divergence on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`, given by the sum
`∑ i |√(x i) - √(y i)|²` on the strictly positive orthant and by `+∞` otherwise. -/
noncomputable def hellingerDivergence (N : ℕ) : ((Fin N → ℝ) × (Fin N → ℝ)) → EReal :=
  fun p ↦
    if ∀ i, 0 < p.1 i ∧ 0 < p.2 i then
      ((∑ i, |Real.sqrt (p.1 i) - Real.sqrt (p.2 i)| ^ 2 : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: unfold `hellingerDivergence` and simplify the defining `if` using the positivity
-- hypothesis on every coordinate of `x` and `y`.
/-- On the strictly positive orthant, the Hellinger divergence is the finite sum
`∑ i |√(x i) - √(y i)|²`. -/
@[simp] theorem hellingerDivergence_apply_of_pos (N : ℕ) (x y : Fin N → ℝ)
    (hxy : ∀ i, 0 < x i ∧ 0 < y i) :
    hellingerDivergence N (x, y) =
      ((∑ i, |Real.sqrt (x i) - Real.sqrt (y i)| ^ 2 : ℝ) : EReal) := by
  -- On the positive orthant, the definition reduces to its explicit finite sum.
  simp [hellingerDivergence, hxy]

/-- Helper for Example 8.30: the positive-weighted scalar Hellinger entropy matches the textbook
coordinate summand. -/
private lemma mul_hellingerEntropy_div_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y * |Real.sqrt (x / y) - 1| ^ 2 = |Real.sqrt x - Real.sqrt y| ^ 2 := by
  have hy_sqrt_ne : Real.sqrt y ≠ 0 := Real.sqrt_ne_zero'.2 hy
  -- Rewrite the ratio under the square root, then clear the positive denominator `√y`.
  rw [sq_abs, sq_abs, Real.sqrt_div hx.le]
  have hy_sq : (Real.sqrt y)^2 = y := by
    nlinarith [Real.sq_sqrt hy.le]
  rw [← hy_sq]
  field_simp [hy_sqrt_ne]
  simp

-- Proof sketch: for `y_i > 0`, rewrite
-- `y_i * hellingerEntropy (x_i / y_i) = |√(x_i) - √(y_i)|²`; if some `x_i ≤ 0`, then
-- `hellingerEntropy (x_i / y_i) = +∞`, so both sides are `+∞`. This identifies the displayed
-- source-facing formula with the coordinate perspective sum from Example 8.26.
/-- The Hellinger divergence is the coordinate perspective sum associated with the Hellinger
entropy. -/
theorem hellingerDivergence_eq_coordinatePerspectiveSum (N : ℕ) :
    hellingerDivergence N = coordinatePerspectiveSum (Fin N) hellingerEntropy := by
  funext p
  rcases p with ⟨x, y⟩
  by_cases hy : ∀ i, 0 < y i
  · by_cases hx : ∀ i, 0 < x i
    · rw [hellingerDivergence_apply_of_pos N x y (fun i ↦ ⟨hx i, hy i⟩)]
      rw [coordinatePerspectiveSum_apply_of_pos (Fin N) hellingerEntropy x y hy]
      have hsum_real :
          ∑ i, y i * |Real.sqrt (x i / y i) - 1| ^ 2 =
            ∑ i, |Real.sqrt (x i) - Real.sqrt (y i)| ^ 2 := by
        -- On the strictly positive orthant, every coordinate term is exactly the scalar
        -- perspective identity.
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact mul_hellingerEntropy_div_eq (hx i) (hy i)
      have hsum_ereal :
          ∑ i, (y i : EReal) * hellingerEntropy (x i / y i) =
            ((∑ i, y i * |Real.sqrt (x i / y i) - 1| ^ 2 : ℝ) : EReal) := by
        calc
          ∑ i, (y i : EReal) * hellingerEntropy (x i / y i)
              = ∑ i, ((y i * |Real.sqrt (x i / y i) - 1| ^ 2 : ℝ) : EReal) := by
                  -- Each positive coordinate stays on the finite branch of `hellingerEntropy`.
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hdiv_pos : 0 < x i / y i := div_pos (hx i) (hy i)
                  rw [hellingerEntropy_apply_of_pos hdiv_pos]
                  norm_num
          _ = ((∑ i, y i * |Real.sqrt (x i / y i) - 1| ^ 2 : ℝ) : EReal) := by
                -- Repackage the finite `EReal` sum as the cast of a real sum.
                symm
                exact ereal_coe_sum_eq_sum_coe _
      -- Both sides now reduce to the same cast real sum.
      calc
        ((∑ i, |Real.sqrt (x i) - Real.sqrt (y i)| ^ 2 : ℝ) : EReal)
            = ((∑ i, y i * |Real.sqrt (x i / y i) - 1| ^ 2 : ℝ) : EReal) := by
                exact_mod_cast hsum_real.symm
        _ = ∑ i, (y i : EReal) * hellingerEntropy (x i / y i) := hsum_ereal.symm
    · have hx_nonpos : ∃ i, x i ≤ 0 := by
        classical
        -- If no coordinate were nonpositive, then all coordinates would be positive, contradicting
        -- the current branch.
        by_contra hx_nonpos
        apply hx
        intro i
        exact lt_of_not_ge (fun hxi_nonpos ↦ hx_nonpos ⟨i, hxi_nonpos⟩)
      have hxy : ¬ ∀ i, 0 < x i ∧ 0 < y i := by
        intro h
        exact hx (fun i ↦ (h i).1)
      rcases hx_nonpos with ⟨i, hxi_nonpos⟩
      rw [hellingerDivergence, if_neg hxy]
      rw [coordinatePerspectiveSum_apply_of_pos (Fin N) hellingerEntropy x y hy]
      have hdiv_nonpos : x i / y i ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hxi_nonpos (hy i).le
      have hterm_top :
          (y i : EReal) * hellingerEntropy (x i / y i) = ⊤ := by
        -- A nonpositive ratio lands in the `+∞` branch of the scalar entropy.
        rw [hellingerEntropy, if_neg (not_lt_of_ge hdiv_nonpos)]
        exact EReal.coe_mul_top_of_pos (hy i)
      symm
      by_contra hsum_ne_top
      have hcoord_ne_top :
          ∀ j ∈ (Finset.univ : Finset (Fin N)),
            (y j : EReal) * hellingerEntropy (x j / y j) ≠ ⊤ := by
        -- If the whole finite sum were finite, each coordinate term would have to be finite.
        exact
          (finset_sum_ne_top_iff_of_forall_ne_bot_local
            (s := (Finset.univ : Finset (Fin N)))
            (a := fun j ↦ (y j : EReal) * hellingerEntropy (x j / y j))
            (fun j _ ↦ scaled_hellingerEntropy_ne_bot (hy j))).1 hsum_ne_top
      exact (hcoord_ne_top i (by simp)) hterm_top
  · have hxy : ¬ ∀ i, 0 < x i ∧ 0 < y i := by
      intro hxy
      exact hy (fun i ↦ (hxy i).2)
    -- If some coordinate of `y` is nonpositive, both definitions are already `⊤`.
    simp [hellingerDivergence, coordinatePerspectiveSum, hy, hxy]

-- Proof sketch: combine `hellingerDivergence_eq_coordinatePerspectiveSum` with Example 8.26,
-- applied to `hellingerEntropy`, and use `convex_epigraph_hellingerEntropy` for the scalar
-- convexity hypothesis.
/-- Example 8.30: the Hellinger divergence on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`,
defined by `∑ i |√(x i) - √(y i)|²` on the strictly positive orthant and by `+∞` otherwise, has
convex epigraph. -/
theorem convex_epigraph_hellingerDivergence (N : ℕ) :
    Convex ℝ (epigraph (hellingerDivergence N)) := by
  have hscalar :
      Convex ℝ {p : ℝ × ℝ | hellingerEntropy p.1 ≤ (p.2 : EReal)} := by
    -- Repackage the scalar convexity result in the set form required by Example 8.26.
    simpa [epigraph] using convex_epigraph_hellingerEntropy
  let lift :
      (∀ t, hellingerEntropy t ≠ ⊥) →
      Convex ℝ {p : ℝ × ℝ | hellingerEntropy p.1 ≤ (p.2 : EReal)} →
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) hellingerEntropy p.1 ≤ (p.2 : EReal)} :=
    ERealFunction.convex_coordinatePerspectiveSum (Fin N) hellingerEntropy
  let hsum :
      Convex ℝ {p : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) |
        coordinatePerspectiveSum (Fin N) hellingerEntropy p.1 ≤ (p.2 : EReal)} :=
    lift hellingerEntropy_ne_bot hscalar
  -- Example 8.26 finishes once the Hellinger divergence is identified with the coordinate
  -- perspective sum.
  simpa [hellingerDivergence_eq_coordinatePerspectiveSum, epigraph] using hsum

end ERealFunction
