/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Proposition 8.13: strict convexity forces the effective domain to be convex. -/
private lemma effectiveDomain_convex_of_strictlyConvex (f : H → Set.Ioi (⊥ : EReal))
    (hf : StrictlyConvex f) : Convex ℝ (effectiveDomain f) := by
  -- Route correction: instead of inducting directly on finite families, first show that strict
  -- convexity makes `effectiveDomain f` itself convex, so later finite Jensen steps can use
  -- mathlib's strict-convexity API on a real-valued model of `f`.
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  by_cases hxy : x = y
  · have hsame : a • x + b • x = x := by
      calc
        a • x + b • x = (a + b) • x := by rw [add_smul]
        _ = x := by simp [hab]
    subst hxy
    simpa [hsame] using hx
  · rw [mem_effectiveDomain_iff]
    have hb_eq : b = 1 - a := by
      linarith
    have hineq := hf hx hy hxy ha (by nlinarith)
    have hxtop : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
    have hytop : (f y : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hy)
    have hxbot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hybot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    -- Rewrite the strict Jensen upper bound into a genuine real value to certify finiteness.
    calc
      (f (a • x + b • y) : EReal) <
          (a : EReal) * (f x : EReal) + ((1 - a : ℝ) : EReal) * (f y : EReal) := by
            simpa [hb_eq] using hineq
      _ = ((a * (f x : EReal).toReal + (1 - a) * (f y : EReal).toReal : ℝ) : EReal) := by
            rw [← EReal.coe_toReal hxtop hxbot, ← EReal.coe_toReal hytop hybot,
              ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
            simp
      _ = ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
            simp [hb_eq]
      _ < ⊤ := EReal.coe_lt_top _

/-- Helper for Proposition 8.13: after passing to `toReal` on the effective domain, a strictly
convex `]-∞,+∞]`-valued function becomes a mathlib `StrictConvexOn` real-valued function. -/
private lemma toReal_strictConvexOn_effectiveDomain (f : H → Set.Ioi (⊥ : EReal))
    (hf : StrictlyConvex f) :
    StrictConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) := by
  -- The source proof's two-point strict inequality is exactly the hypothesis needed to build the
  -- real-valued strict-convex structure on the effective domain.
  rw [strictConvexOn_iff_div]
  refine ⟨effectiveDomain_convex_of_strictlyConvex f hf, ?_⟩
  intro x hx y hy hxy a b ha hb
  have hab_pos : 0 < a + b := add_pos ha hb
  have ha' : 0 < a / (a + b) := div_pos ha hab_pos
  have hb' : 0 < b / (a + b) := div_pos hb hab_pos
  have hb_eq : b / (a + b) = 1 - a / (a + b) := by
    field_simp [hab_pos.ne']
    ring
  have hineq := hf hx hy hxy ha' (by simpa [hb_eq] using hb')
  have hconv := effectiveDomain_convex_of_strictlyConvex f hf
  have hmem : (a / (a + b)) • x + (b / (a + b)) • y ∈ effectiveDomain f := by
    have hsum_div : a / (a + b) + b / (a + b) = 1 := by
      field_simp [hab_pos.ne']
    simpa using
      (convex_iff_add_mem.mp hconv) hx hy (le_of_lt ha') (le_of_lt hb') hsum_div
  have hleft_top :
      (f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal) ≠ ⊤ :=
    ne_of_lt ((mem_effectiveDomain_iff).mp hmem)
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hy)
  have hleft_bot :
      (f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) <
      (f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal) from (f _).2)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hineqE :
      (f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal) <
        ((((a / (a + b)) * (f x : EReal).toReal +
            (b / (a + b)) * (f y : EReal).toReal : ℝ) : EReal)) := by
    -- Convert the EReal-valued strict inequality into a strict inequality between real casts.
    calc
      (f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal)
          < ((a / (a + b) : ℝ) : EReal) * (f x : EReal) +
              ((1 - a / (a + b) : ℝ) : EReal) * (f y : EReal) := by
                simpa [hb_eq] using hineq
      _ = ((((a / (a + b)) * (f x : EReal).toReal +
            (1 - a / (a + b)) * (f y : EReal).toReal : ℝ) : EReal)) := by
            rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
              ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
            simp
      _ = ((((a / (a + b)) * (f x : EReal).toReal +
            (b / (a + b)) * (f y : EReal).toReal : ℝ) : EReal)) := by
            simp [hb_eq]
  have hleft_eq :
      (((f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal)).toReal : EReal) =
        (f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal) :=
    EReal.coe_toReal hleft_top hleft_bot
  have hltE :
      (((f ((a / (a + b)) • x + (b / (a + b)) • y) : EReal)).toReal : EReal) <
        ((((a / (a + b)) * (f x : EReal).toReal +
            (b / (a + b)) * (f y : EReal).toReal : ℝ) : EReal)) := by
    simpa [hleft_eq] using hineqE
  exact EReal.coe_lt_coe_iff.mp hltE

/-- Helper for Proposition 8.13: each weighted value term of an effective-domain point is the cast
of the corresponding real product after applying `toReal`. -/
private lemma weighted_value_term_eq_coe_toReal (f : H → Set.Ioi (⊥ : EReal))
    {x : H} (hx : x ∈ effectiveDomain f) (a : ℝ) :
    (a : EReal) * (f x : EReal) = ((a * (f x : EReal).toReal : ℝ) : EReal) := by
  -- Domain membership removes `⊤`, while the codomain removes `⊥`, so the term is literally a
  -- cast of a real product.
  have hxtop : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hxbot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  rw [← EReal.coe_toReal hxtop hxbot, ← EReal.coe_mul]
  simp

/-- Helper for Proposition 8.13: the finite weighted value sum over effective-domain points is the
cast of the corresponding real sum of `toReal` values. -/
private lemma weighted_value_sum_eq_coe_sum_toReal (f : H → Set.Ioi (⊥ : EReal))
    {I : Type v} (s : Finset I) (α : I → ℝ) (x : I → H)
    (hdom : ∀ i ∈ s, x i ∈ effectiveDomain f) :
    (∑ i ∈ s, (α i : EReal) * (f (x i) : EReal)) =
      ((∑ i ∈ s, α i * (f (x i) : EReal).toReal : ℝ) : EReal) := by
  -- Expand the finite sum termwise, using the previous one-point conversion lemma at each index.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
      · rw [weighted_value_term_eq_coe_toReal f (hdom i (Finset.mem_insert_self i s)) (α i),
          ← EReal.coe_add]
      · intro j hj
        exact hdom j (Finset.mem_insert_of_mem hj)

/-- Helper for Proposition 8.13: if all points of a weighted family are equal to a common value,
then that value is the barycenter of the family. -/
private lemma exists_constant_iff_eq_barycenter {I : Type v} (s : Finset I) (α : I → ℝ) (x : I → H)
    (hsum : ∑ i ∈ s, α i = 1) :
    (∃ y, ∀ i ∈ s, x i = y) ↔ ∀ i ∈ s, x i = ∑ i ∈ s, α i • x i := by
  let barycenter := ∑ i ∈ s, α i • x i
  constructor
  · intro hconst i hi
    rcases hconst with ⟨y, hy⟩
    have hbary : barycenter = y := by
      -- A constant weighted family collapses to the common value because the weights sum to `1`.
      calc
        barycenter = ∑ j ∈ s, α j • y := by
          simp only [barycenter]
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [hy j hj]
        _ = (∑ j ∈ s, α j) • y := by
          symm
          exact Finset.sum_smul
        _ = y := by
          simp [hsum]
    simpa [barycenter, hbary] using hy i hi
  · intro hbary
    exact ⟨barycenter, hbary⟩

-- Proof sketch: prove the forward implication by induction on the finite index set, reducing the
-- last step to the binary strict-convexity inequality from the definition. For the converse,
-- specialize the finite-family statement to a two-point family with weights `α` and `1 - α`.
/-- Proposition 8.13: strict convexity is equivalent to the finite Jensen inequality on the
effective domain together with the equality characterization that forces the weighted family to be
constant, equivalently to have singleton image. -/
theorem strictlyConvex_iff_finset_jensen_le_and_eq_iff_constant
    (f : H → Set.Ioi (⊥ : EReal)) :
    StrictlyConvex f ↔
      ∀ {I : Type v} (s : Finset I) (α : I → ℝ) (x : I → H),
        (∀ i ∈ s, α i ∈ Set.Ioo (0 : ℝ) 1) →
        (∑ i ∈ s, α i = 1) →
        (∀ i ∈ s, x i ∈ effectiveDomain f) →
          (f (∑ i ∈ s, α i • x i) : EReal) ≤
              ∑ i ∈ s, (α i : EReal) * (f (x i) : EReal) ∧
            ((f (∑ i ∈ s, α i • x i) : EReal) =
                ∑ i ∈ s, (α i : EReal) * (f (x i) : EReal) ↔
              ∃ y, ∀ i ∈ s, x i = y) := by
  constructor
  · intro hf I s α x hα hsum hdom
    let barycenter : H := ∑ i ∈ s, α i • x i
    let g : H → ℝ := fun z ↦ (f z : EReal).toReal
    have hg : StrictConvexOn ℝ (effectiveDomain f) g :=
      toReal_strictConvexOn_effectiveDomain f hf
    have hconv : Convex ℝ (effectiveDomain f) :=
      effectiveDomain_convex_of_strictlyConvex f hf
    have hα_nonneg : ∀ i ∈ s, 0 ≤ α i := by
      intro i hi
      exact (hα i hi).1.le
    have hbary_dom : barycenter ∈ effectiveDomain f := by
      -- The convexity of the effective domain keeps the barycenter inside the domain.
      exact hconv.sum_mem hα_nonneg hsum hdom
    have hreal_le :
        g barycenter ≤ ∑ i ∈ s, α i * g (x i) := by
      -- Apply mathlib's finite Jensen inequality to the real-valued strict-convex model.
      exact hg.convexOn.map_sum_le hα_nonneg hsum hdom
    have hvalue_sum :
        (∑ i ∈ s, (α i : EReal) * (f (x i) : EReal)) =
          ((∑ i ∈ s, α i * g (x i) : ℝ) : EReal) := by
      simpa [g] using weighted_value_sum_eq_coe_sum_toReal f s α x hdom
    have hbary_top : (f barycenter : EReal) ≠ ⊤ := by
      exact ne_of_lt ((mem_effectiveDomain_iff).mp hbary_dom)
    have hbary_bot : (f barycenter : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f barycenter : EReal) from (f barycenter).2)
    have hbary_eq :
        (((f barycenter : EReal).toReal : ℝ) : EReal) = (f barycenter : EReal) :=
      EReal.coe_toReal hbary_top hbary_bot
    have hle :
        (f barycenter : EReal) ≤ ∑ i ∈ s, (α i : EReal) * (f (x i) : EReal) := by
      -- Recast the real Jensen inequality back into `EReal`.
      calc
        (f barycenter : EReal) = (((f barycenter : EReal).toReal : ℝ) : EReal) := by
          symm
          exact hbary_eq
        _ ≤ ((∑ i ∈ s, α i * g (x i) : ℝ) : EReal) := by
          exact EReal.coe_le_coe hreal_le
        _ = ∑ i ∈ s, (α i : EReal) * (f (x i) : EReal) := by
          symm
          exact hvalue_sum
    have hsum_top :
        (∑ i ∈ s, (α i : EReal) * (f (x i) : EReal)) ≠ ⊤ := by
      rw [hvalue_sum]
      exact ne_of_lt (EReal.coe_lt_top _)
    have hsum_bot :
        (∑ i ∈ s, (α i : EReal) * (f (x i) : EReal)) ≠ ⊥ := by
      rw [hvalue_sum]
      simp
    have hEq_real :
        g barycenter = ∑ i ∈ s, α i * g (x i) ↔
          ∀ i ∈ s, x i = barycenter := by
      -- Equality in Jensen's inequality for a strictly convex function forces every point to equal
      -- the barycenter.
      exact hg.map_sum_eq_iff (fun i hi ↦ (hα i hi).1) hsum hdom
    have hEq_ereal_real :
        (f barycenter : EReal) = ∑ i ∈ s, (α i : EReal) * (f (x i) : EReal) ↔
          g barycenter = ∑ i ∈ s, α i * g (x i) := by
      -- Both sides are finite, so equality in `EReal` is equivalent to equality after `toReal`.
      have htoReal :=
        (EReal.toReal_eq_toReal hbary_top hbary_bot hsum_top hsum_bot).symm
      simpa [g, hvalue_sum] using htoReal
    refine ⟨hle, ?_⟩
    -- The equality criterion is the conjunction of the real-valued strict Jensen equality theorem
    -- and the elementary fact that a family is constant iff each term equals its barycenter.
    calc
      (f barycenter : EReal) = ∑ i ∈ s, (α i : EReal) * (f (x i) : EReal)
          ↔ g barycenter = ∑ i ∈ s, α i * g (x i) := hEq_ereal_real
      _ ↔ ∀ i ∈ s, x i = barycenter := hEq_real
      _ ↔ ∃ y, ∀ i ∈ s, x i = y := by
        rw [exists_constant_iff_eq_barycenter s α x hsum]
  · intro hstrict x hx y hy hxy α hα hα_lt_one
    let s2 : Finset (ULift (Fin 2)) := {⟨0⟩, ⟨1⟩}
    let β : ULift (Fin 2) → ℝ := fun i ↦ ![α, 1 - α] i.down
    let p : ULift (Fin 2) → H := fun i ↦ ![x, y] i.down
    have hβ_mem : ∀ i ∈ s2, β i ∈ Set.Ioo (0 : ℝ) 1 := by
      intro i _
      rcases i with ⟨i⟩
      fin_cases i <;> simp [β, hα, hα_lt_one, sub_pos.mpr hα_lt_one]
    have hβ_sum : ∑ i ∈ s2, β i = 1 := by
      simp [s2, β]
    have hp_dom : ∀ i ∈ s2, p i ∈ effectiveDomain f := by
      intro i _
      rcases i with ⟨i⟩
      fin_cases i
      · simpa [p] using hx
      · simpa [p] using hy
    have hfamily :=
      hstrict (I := ULift (Fin 2)) s2 β p hβ_mem hβ_sum hp_dom
    have hle_pair :
        (f (α • x + (1 - α) • y) : EReal) ≤
          (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
      simpa [s2, β, p, add_comm, add_left_comm, add_assoc] using hfamily.1
    have hneq_pair :
        (f (α • x + (1 - α) • y) : EReal) ≠
          (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
      intro hEq
      have hconst : ∃ z, ∀ i ∈ s2, p i = z :=
        (hfamily.2.mp (by simpa [s2, β, p, add_comm, add_left_comm, add_assoc] using hEq))
      rcases hconst with ⟨z, hz⟩
      have hxz : x = z := by
        simpa [s2, p] using hz ⟨0⟩ (by simp [s2])
      have hyz : y = z := by
        simpa [s2, p] using hz ⟨1⟩ (by simp [s2])
      exact hxy (hxz.trans hyz.symm)
    -- Equality is excluded by the two-point instance of the finite-family hypothesis, so the
    -- Jensen inequality is automatically strict.
    exact lt_of_le_of_ne hle_pair hneq_pair

end ERealFunction
