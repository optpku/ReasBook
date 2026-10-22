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

variable {ι : Type*} [Fintype ι]

/-- The scalar power generator `t ↦ t^α` on `]0,+∞[` extended by `+∞` on `]-∞,0]`. -/
noncomputable def powerGenerator (α : ℝ) : ℝ → EReal :=
  fun t ↦ if 0 < t then ((t ^ α : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `powerGenerator` and simplify the defining `if` using `0 < t`.
/-- On the positive half-line, `powerGenerator α` evaluates to `t ^ α`. -/
@[simp] theorem powerGenerator_apply_of_pos {α t : ℝ} (ht : 0 < t) :
    powerGenerator α t = ((t ^ α : ℝ) : EReal) := by
  -- On `Set.Ioi 0`, the extended-valued definition reduces to the real power branch.
  simp [powerGenerator, ht]

-- Proof sketch: unfold `powerGenerator` and simplify the defining `if` using `¬ 0 < t`,
-- obtained from `t ≤ 0`.
/-- On the nonpositive half-line, `powerGenerator α` evaluates to `+∞`. -/
@[simp] theorem powerGenerator_apply_of_nonpos {α t : ℝ} (ht : t ≤ 0) :
    powerGenerator α t = ⊤ := by
  -- Outside the positive half-line, the defining `if` forces the value to be `+∞`.
  simp [powerGenerator, not_lt_of_ge ht]

/-- Helper for Example 8.31: real-height epigraph membership for the scalar power generator is
equivalent to strict positivity together with the corresponding power inequality. -/
private lemma mem_epigraph_powerGenerator_iff {α t r : ℝ} :
    (t, r) ∈ epigraph (powerGenerator α) ↔ 0 < t ∧ t ^ α ≤ r := by
  constructor
  · intro h
    rw [mem_epigraph_iff] at h
    by_cases ht : 0 < t
    · constructor
      · exact ht
      · have h' : (((t ^ α : ℝ) : EReal)) ≤ (r : EReal) := by
          -- On the positive branch, the `EReal` inequality is just the cast of the real bound.
          simpa [powerGenerator, ht] using h
        exact_mod_cast h'
    · have htop := h
      -- If `t` is not positive, the scalar generator is `⊤`, which no real height can dominate.
      simp [powerGenerator, ht] at htop
  · rintro ⟨ht, htr⟩
    rw [mem_epigraph_iff]
    have h' : (((t ^ α : ℝ) : EReal)) ≤ (r : EReal) := by
      -- Cast the real inequality into `EReal` before returning to the positive branch.
      exact_mod_cast htr
    simpa [powerGenerator, ht] using h'

/-- Helper for Example 8.31: the scalar power generator never takes the value `-∞`. -/
private theorem powerGenerator_ne_bot (α : ℝ) (t : ℝ) :
    powerGenerator α t ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- On the positive branch the value is a real number, hence not `-∞`.
    rw [powerGenerator_apply_of_pos ht]
    exact EReal.coe_ne_bot _
  · -- On the complementary branch the value is `⊤`.
    simp [powerGenerator, ht]

-- Proof sketch: apply the canonical one-variable convexity result `convexOn_rpow` for
-- `t ↦ t ^ α` on `Set.Ici 0` when `1 ≤ α`, restrict it to `Set.Ioi 0`, and then identify the
-- textbook extension by `+∞` outside `Set.Ioi 0` with the
-- real-height epigraph formulation used in Chapter 8.
/-- The scalar power generator has convex real-height epigraph for exponents `α ≥ 1`. -/
theorem convex_epigraph_powerGenerator (α : ℝ) (hα : 1 ≤ α) :
    Convex ℝ (epigraph (powerGenerator α)) := by
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, ξ⟩
  rcases q with ⟨y, η⟩
  rw [mem_epigraph_powerGenerator_iff] at hp hq
  rw [mem_epigraph_powerGenerator_iff]
  constructor
  · -- Strict positivity of the scalar argument is preserved by convex combinations.
    simpa [Prod.smul_mk, smul_eq_mul] using add_pos (mul_pos ha hp.1) (mul_pos hb hq.1)
  · have hpower :
        (a * x + b * y) ^ α ≤ a * x ^ α + b * y ^ α :=
      (convexOn_rpow hα).2
        (show x ∈ Set.Ici (0 : ℝ) from hp.1.le)
        (show y ∈ Set.Ici (0 : ℝ) from hq.1.le)
        ha.le hb.le hab
    have hheight :
        a * x ^ α + b * y ^ α ≤ a * ξ + b * η := by
      -- The endpoint epigraph inequalities scale and add because the coefficients are
      -- nonnegative.
      exact add_le_add (mul_le_mul_of_nonneg_left hp.2 ha.le)
        (mul_le_mul_of_nonneg_left hq.2 hb.le)
    -- The branchwise convexity of `t ↦ t ^ α` and the endpoint height bounds yield the barycenter
    -- epigraph inequality.
    exact le_trans hpower hheight

/-- The textbook function
`(x, y) ↦ ∑ i, x i ^ α * y i ^ (1 - α)` on the positive orthant of a finite family, extended by
`+∞` outside that orthant. Specializing `ι` to `Fin N` recovers the canonical coordinate model of
`ℝ^N × ℝ^N`. -/
noncomputable def powerPerspectiveDivergence (ι : Type*) [Fintype ι] (α : ℝ) :
    ((ι → ℝ) × (ι → ℝ)) → EReal :=
  coordinatePerspectiveSum ι (powerGenerator α)

/-- Helper for Example 8.31: coercing a finite real sum into `EReal` agrees with summing the
coerced terms. -/
private lemma ereal_coe_sum_eq_sum_coe {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) := by
  classical
  -- Expand the finite sum inductively and use compatibility of the coercion with addition.
  let s : Finset ι := Finset.univ
  change (((s.sum fun i ↦ f i : ℝ)) : EReal) = s.sum fun i ↦ (f i : EReal)
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

-- Proof sketch: unfold `powerPerspectiveDivergence` as the coordinate perspective sum attached to
-- `powerGenerator α`; on the strictly positive orthant, rewrite each coordinate term
-- `y i * (x i / y i) ^ α` as `x i ^ α * y i ^ (1 - α)`.
/-- On the strictly positive orthant, the power perspective divergence is the finite sum
`∑ i, x i ^ α * y i ^ (1 - α)`. -/
theorem powerPerspectiveDivergence_apply_of_pos (ι : Type*) [Fintype ι] (α : ℝ) (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    powerPerspectiveDivergence ι α (x, y) =
      ((∑ i, (x i) ^ α * (y i) ^ (1 - α) : ℝ) : EReal) := by
  rw [powerPerspectiveDivergence]
  rw [coordinatePerspectiveSum_apply_of_pos ι (powerGenerator α) x y hy]
  calc
    ∑ i, (y i : EReal) * powerGenerator α (x i / y i)
        = ∑ i, ((y i * (x i / y i) ^ α : ℝ) : EReal) := by
            -- Each coordinate stays on the positive branch of `powerGenerator`.
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hdiv_pos : 0 < x i / y i := div_pos (hx i) (hy i)
            rw [powerGenerator_apply_of_pos hdiv_pos, EReal.coe_mul]
    _ = ((∑ i, y i * (x i / y i) ^ α : ℝ) : EReal) := by
          -- Repackage the finite `EReal` sum as the cast of a real sum.
          symm
          exact ereal_coe_sum_eq_sum_coe (fun i ↦ y i * (x i / y i) ^ α)
    _ = ((∑ i, (x i) ^ α * (y i) ^ (1 - α) : ℝ) : EReal) := by
          have hsum_real :
              (∑ i, y i * (x i / y i) ^ α : ℝ) =
                ∑ i, (x i) ^ α * (y i) ^ (1 - α) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              y i * (x i / y i) ^ α
                  = y i * (x i ^ α / y i ^ α) := by
                      rw [Real.div_rpow (hx i).le (hy i).le α]
              _ = y i * (x i ^ α * (y i ^ α)⁻¹) := by
                    rw [div_eq_mul_inv]
              _ = (x i) ^ α * (y i * (y i ^ α)⁻¹) := by
                    ring
              _ = (x i) ^ α * (y i / y i ^ α) := by
                    rw [div_eq_mul_inv]
              _ = (x i) ^ α * (y i) ^ (1 - α) := by
                    have hy_rpow :
                        y i / y i ^ α = (y i) ^ (1 - α) := by
                      simpa [Real.rpow_one] using (Real.rpow_sub (hy i) 1 α).symm
                    rw [hy_rpow]
          exact congrArg (fun r : ℝ ↦ (r : EReal)) hsum_real

-- Proof sketch: apply Example 8.26 to `powerGenerator α`. The required scalar convexity is
-- `convex_epigraph_powerGenerator α hα`, and the source-facing formula on the positive orthant is
-- given by `powerPerspectiveDivergence_apply_of_pos`.
/-- Example 8.31: for `α ≥ 1`, the finite-index function that equals
`∑ i, x i ^ α * y i ^ (1 - α)` on the strictly positive orthant and `+∞` otherwise has convex
real-height epigraph. -/
theorem convex_epigraph_powerPerspectiveDivergence (ι : Type*) [Fintype ι]
    (α : ℝ) (hα : 1 ≤ α) :
    Convex ℝ (epigraph (powerPerspectiveDivergence ι α)) := by
  have hscalar :
      Convex ℝ {p : ℝ × ℝ | powerGenerator α p.1 ≤ (p.2 : EReal)} := by
    -- Repackage the scalar epigraph result in the set form expected by Example 8.26.
    simpa [epigraph] using convex_epigraph_powerGenerator α hα
  let lift :
      (∀ t, powerGenerator α t ≠ ⊥) →
      Convex ℝ {p : ℝ × ℝ | powerGenerator α p.1 ≤ (p.2 : EReal)} →
      Convex ℝ {p : (((ι → ℝ) × (ι → ℝ)) × ℝ) |
        coordinatePerspectiveSum ι (powerGenerator α) p.1 ≤ (p.2 : EReal)} :=
    ERealFunction.convex_coordinatePerspectiveSum ι (powerGenerator α)
  let hsum :
      Convex ℝ {p : (((ι → ℝ) × (ι → ℝ)) × ℝ) |
        coordinatePerspectiveSum ι (powerGenerator α) p.1 ≤ (p.2 : EReal)} :=
    lift (powerGenerator_ne_bot α) hscalar
  -- Example 8.26 lifts scalar epigraph convexity to the coordinate perspective sum.
  simpa [powerPerspectiveDivergence, epigraph] using hsum

end ERealFunction
