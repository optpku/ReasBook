/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped BigOperators

universe u v

namespace ERealFunction

attribute [local instance] Classical.propDecidable

variable {I : Type v} {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

/-- The function obtained from a family of coordinate functions on a Hilbert sum by taking the
ordinary total sum when the index type is finite, and otherwise the supremum of all finite partial
sums. -/
noncomputable def hilbertSumFunction (f : ∀ i, H i → EReal) : lp H 2 → EReal :=
  fun x ↦
    if _hI : Finite I then
      let _ : Fintype I := Fintype.ofFinite I
      ∑ i, f i (x i)
    else
      sSup (Set.range fun J : Finset I ↦ J.sum (fun i ↦ f i (x i)))

/- The textbook direct-sum surface `⨁ i, f i` for coordinate functions on a Hilbert sum. -/
scoped[ERealFunction] notation3 "⨁ "(...)", " r:(scoped f => hilbertSumFunction f) => r

-- Proof sketch: unfold `hilbertSumFunction` and simplify the finite branch of the defining `if`.
/-- For a finite index type, `hilbertSumFunction` is the ordinary sum of the coordinate
functions. -/
theorem hilbertSumFunction_apply_of_finite (f : ∀ i, H i → EReal) [Finite I] (x : lp H 2) :
    (⨁ i, f i) x =
      (let _ : Fintype I := Fintype.ofFinite I
       ∑ i, f i (x i)) := by
  -- In the finite branch, the defining `if` picks the ordinary total sum.
  have hI : Finite I := inferInstance
  simp [hilbertSumFunction, hI]

-- Proof sketch: unfold `hilbertSumFunction` and simplify the infinite branch of the defining
-- `if`.
/-- For an infinite index type, `hilbertSumFunction` is the supremum of its finite partial sums. -/
theorem hilbertSumFunction_apply_of_infinite (f : ∀ i, H i → EReal) [Infinite I] (x : lp H 2) :
    (⨁ i, f i) x = sSup (Set.range fun J : Finset I ↦ J.sum (fun i ↦ f i (x i))) := by
  -- In the infinite branch, the defining `if` reduces to the supremum of finite partial sums.
  have hI : ¬ Finite I := not_finite_iff_infinite.mpr inferInstance
  simp [hilbertSumFunction, hI]

section JensenBridge

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 8.6: a point of the effective domain admits a real epigraph height. -/
private lemma exists_real_ge_of_mem_dom_local (g : X → EReal) {x : X} (hx : x ∈ dom g) :
    ∃ ξ : ℝ, g x ≤ (ξ : EReal) := by
  -- Domain membership means exactly that `g x` lies strictly below `⊤`.
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 8.6: a real-height epigraph point has base point in the effective
domain. -/
private lemma mem_dom_of_mem_epigraph_local (g : X → EReal) {x : X} {ξ : ℝ}
    (hξ : (x, ξ) ∈ epigraph g) : x ∈ dom g := by
  -- A real epigraph ordinate bounds `g x` by something strictly below `⊤`.
  rw [mem_epigraph_iff] at hξ
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hξ (EReal.coe_lt_top ξ)

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 8.6: a finite-above non-`⊥` value yields a canonical real epigraph
point via `toReal`. -/
private lemma mem_epigraph_toReal_of_mem_dom_of_ne_bot_local
    (g : X → EReal) {x : X} (hx : x ∈ dom g) (hbot : g x ≠ ⊥) :
    (x, (g x).toReal) ∈ epigraph g := by
  -- The `toReal` coordinate lands exactly at `g x` once both infinities are excluded.
  have htop : g x ≠ ⊤ := ne_of_lt ((mem_dom_iff g x).mp hx)
  simp [mem_epigraph_iff, EReal.coe_toReal htop hbot]

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 8.6: if the left endpoint has value `⊥`, convexity of the epigraph
pushes every strict convex combination with a finite point back to `⊥`. -/
private lemma combo_value_eq_bot_of_left_bot_of_convex_epigraph_local
    (g : X → EReal) (hconv : Convex ℝ (epigraph g)) {x y : X} (hgx : g x = ⊥)
    (hy : y ∈ dom g) {α : ℝ} (hα : 0 < α) (hα_lt_one : α < 1) :
    g (α • x + (1 - α) • y) = ⊥ := by
  -- Route correction: when the left endpoint is `⊥`, use arbitrary real heights above it and
  -- drive the convex-combination height below every prescribed real bound.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  rcases exists_real_ge_of_mem_dom_local g hy with ⟨ξ, hξ⟩
  let η : ℝ := (r - (1 - α) * ξ) / α - 1
  have hx_mem : (x, η) ∈ epigraph g := by
    -- Any real ordinate lies above `⊥`.
    rw [mem_epigraph_iff, hgx]
    simp
  have hy_mem : (y, ξ) ∈ epigraph g := by
    -- The domain witness gives a genuine real-height epigraph point at `y`.
    simpa [mem_epigraph_iff] using hξ
  have hβ : 0 < 1 - α := sub_pos.mpr hα_lt_one
  have hcombo_mem :
      (α • (x, η) + (1 - α) • (y, ξ)) ∈ epigraph g := by
    -- Convexity propagates membership to the strict convex combination.
    exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem hα hβ (by ring)
  have hcombo_le :
      g (α • x + (1 - α) • y) ≤ ((α * η + (1 - α) * ξ : ℝ) : EReal) := by
    -- Rewrite product-space convexity into the scalar Jensen inequality.
    rw [mem_epigraph_iff] at hcombo_mem
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
  have hη_eq : α * η + (1 - α) * ξ = r - α := by
    -- The chosen `η` makes the combined height exactly `r - α`.
    dsimp [η]
    field_simp [hα.ne']
    ring
  have hheight_lt : ((α * η + (1 - α) * ξ : ℝ) : EReal) < (r : EReal) := by
    -- Since `α > 0`, the height `r - α` lies strictly below `r`.
    rw [hη_eq]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hα)
  exact lt_of_le_of_lt hcombo_le hheight_lt

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)] in
/-- Helper for Proposition 8.6: a local Jensen characterization of convex epigraphs on the
effective domain. This is the file-local bridge used to prove convexity of the Hilbert-sum
function without importing Proposition 8.4 into the item file. -/
private theorem convex_epigraph_iff_jensen_on_dom_local (g : X → EReal) :
    Convex ℝ (epigraph g) ↔
      ∀ ⦃x y : X⦄, x ∈ dom g → y ∈ dom g → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        g (α • x + (1 - α) • y) ≤
          (α : EReal) * g x + (((1 - α : ℝ) : EReal) * g y) := by
  constructor
  · intro hconv x y hx hy α hα hα_lt_one
    by_cases hgx : g x = ⊥
    · -- If the left endpoint is `⊥`, the whole strict segment value is forced to `⊥`.
      have hcombo_bot :
          g (α • x + (1 - α) • y) = ⊥ :=
        combo_value_eq_bot_of_left_bot_of_convex_epigraph_local g hconv hgx hy hα hα_lt_one
      have hαE : 0 < (α : EReal) := EReal.coe_pos.mpr hα
      simp [hcombo_bot, hgx, EReal.mul_bot_of_pos hαE]
    · by_cases hgy : g y = ⊥
      · -- Swap the two endpoints to reduce to the previous `⊥` case.
        have hcombo_bot_swapped :
            g ((1 - α) • y + (1 - (1 - α)) • x) = ⊥ :=
          combo_value_eq_bot_of_left_bot_of_convex_epigraph_local g hconv hgy hx
            (sub_pos.mpr hα_lt_one) (by linarith)
        have hrewrite : 1 - (1 - α) = α := by ring
        have hcombo_bot :
            g (α • x + (1 - α) • y) = ⊥ := by
          simpa [hrewrite, add_comm, add_left_comm, add_assoc] using hcombo_bot_swapped
        simp [hcombo_bot, hgy]
      · -- Once both endpoint values are finite real numbers, the usual `toReal` argument works.
        have hx_mem : (x, (g x).toReal) ∈ epigraph g :=
          mem_epigraph_toReal_of_mem_dom_of_ne_bot_local g hx hgx
        have hy_mem : (y, (g y).toReal) ∈ epigraph g :=
          mem_epigraph_toReal_of_mem_dom_of_ne_bot_local g hy hgy
        have hβ : 0 < 1 - α := sub_pos.mpr hα_lt_one
        have hcombo_mem :
            (α • (x, (g x).toReal) + (1 - α) • (y, (g y).toReal)) ∈ epigraph g := by
          -- Convexity of the epigraph yields the combined real-height point.
          exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem hα hβ (by ring)
        have hcombo_le :
            g (α • x + (1 - α) • y) ≤
              ((α * (g x).toReal + (1 - α) * (g y).toReal : ℝ) : EReal) := by
          -- Expand the product-space convex combination into the desired coordinates.
          rw [mem_epigraph_iff] at hcombo_mem
          simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
        have hxtop : g x ≠ ⊤ := ne_of_lt ((mem_dom_iff g x).mp hx)
        have hytop : g y ≠ ⊤ := ne_of_lt ((mem_dom_iff g y).mp hy)
        calc
          g (α • x + (1 - α) • y)
              ≤ ((α * (g x).toReal + (1 - α) * (g y).toReal : ℝ) : EReal) := hcombo_le
          _ = (α : EReal) * g x + (((1 - α : ℝ) : EReal) * g y) := by
            rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hxtop hgx,
              EReal.coe_toReal hytop hgy]
  · intro hJ
    refine (convex_iff_forall_pos).2 ?_
    intro p hp q hq a b ha hb hab
    rcases p with ⟨x, ξ⟩
    rcases q with ⟨y, η⟩
    have hx : x ∈ dom g := mem_dom_of_mem_epigraph_local g hp
    have hy : y ∈ dom g := mem_dom_of_mem_epigraph_local g hq
    have ha_lt_one : a < 1 := by nlinarith
    have hb_eq : b = 1 - a := by nlinarith
    have haE : 0 < (a : EReal) := EReal.coe_pos.mpr ha
    have hbE : 0 < (b : EReal) := EReal.coe_pos.mpr hb
    have hJxy :
        g (a • x + b • y) ≤ (a : EReal) * g x + ((b : EReal) * g y) := by
      -- Rewrite the second coefficient to fit the Jensen hypothesis.
      simpa [hb_eq] using hJ hx hy ha ha_lt_one
    have hx_le :
        (a : EReal) * g x ≤ (a : EReal) * (ξ : EReal) :=
      mul_le_mul_of_nonneg_left ((mem_epigraph_iff g x ξ).mp hp) haE.le
    have hy_le :
        (b : EReal) * g y ≤ (b : EReal) * (η : EReal) :=
      mul_le_mul_of_nonneg_left ((mem_epigraph_iff g y η).mp hq) hbE.le
    have hsum_le :
        (a : EReal) * g x + (b : EReal) * g y ≤
          (a : EReal) * (ξ : EReal) + (b : EReal) * (η : EReal) :=
      add_le_add hx_le hy_le
    have hfinal :
        g (a • x + b • y) ≤ ((a * ξ + b * η : ℝ) : EReal) := by
      -- Compare the Jensen upper bound with the chosen epigraph heights.
      calc
        g (a • x + b • y)
            ≤ (a : EReal) * g x + (b : EReal) * g y := hJxy
        _ ≤ (a : EReal) * (ξ : EReal) + (b : EReal) * (η : EReal) := hsum_le
        _ = ((a * ξ + b * η : ℝ) : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    -- This is exactly the epigraph condition for the convex combination point.
    rw [mem_epigraph_iff]
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal

end JensenBridge

/-- Helper for Proposition 8.6: a finite sum of values avoiding `⊥` again avoids `⊥`. -/
private lemma finset_sum_ne_bot_of_forall_ne_bot {s : Finset I} {a : I → EReal}
    (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊥ := by
  classical
  -- Induct over the finite set and use that `EReal` addition preserves non-`⊥`.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    rw [Finset.sum_insert his, EReal.add_ne_bot_iff]
    constructor
    · exact hbot i (Finset.mem_insert_self i s)
    · exact ih (fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj))

/-- Helper for Proposition 8.6: under the non-`⊥` hypothesis, a finite `EReal` sum is different
from `⊤` exactly when each summand is. -/
private lemma finset_sum_ne_top_iff_of_forall_ne_bot {s : Finset I} {a : I → EReal}
    (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊤ ↔ ∀ i ∈ s, a i ≠ ⊤ := by
  classical
  -- Induct over the finite index set and apply the two-term `EReal` criterion at each step.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    have hbot_i : a i ≠ ⊥ := hbot i (Finset.mem_insert_self i s)
    have hbot_s : ∀ j ∈ s, a j ≠ ⊥ := fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj)
    have hsum_s_ne_bot : s.sum a ≠ ⊥ := finset_sum_ne_bot_of_forall_ne_bot hbot_s
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

/-- Helper for Proposition 8.6: a nonnegative finite `EReal` scalar distributes across a finite
sum. -/
private lemma mul_finset_sum_of_nonneg_of_ne_top
    (a : EReal) (ha_nonneg : 0 ≤ a) (ha_ne_top : a ≠ ⊤) (s : Finset I) (b : I → EReal) :
    a * s.sum b = s.sum (fun i ↦ a * b i) := by
  classical
  -- This is the finite-sum induction form of `EReal.left_distrib_of_nonneg_of_ne_top`.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his,
      EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top, ih]

/-- Helper for Proposition 8.6: in the finite branch, domain membership for the Hilbert-sum
function forces domain membership in every coordinate. -/
private theorem coordinate_dom_of_mem_dom_hilbertSumFunction_finite
    (f : ∀ i, H i → EReal) (hnoBot : ∀ i x, f i x ≠ ⊥) [Finite I]
    {x : lp H 2} (hx : x ∈ dom (hilbertSumFunction f)) :
    ∀ i, x i ∈ dom (f i) := by
  let _ : Fintype I := Fintype.ofFinite I
  -- Rewrite the finite branch and read off each coordinate from the non-`⊥` total sum.
  have hsum_ne_top : (∑ j, f j (x j)) ≠ ⊤ := by
    rw [mem_dom_iff] at hx
    simpa [hilbertSumFunction_apply_of_finite (f := f) (x := x)] using ne_of_lt hx
  have hcoord_ne_top :
      ∀ j ∈ (Finset.univ : Finset I), f j (x j) ≠ ⊤ := by
    exact
      (finset_sum_ne_top_iff_of_forall_ne_bot
        (s := (Finset.univ : Finset I)) (a := fun j ↦ f j (x j))
        (fun j _ ↦ hnoBot j (x j))).1 hsum_ne_top
  intro i
  rw [mem_dom_iff]
  exact lt_top_iff_ne_top.mpr (hcoord_ne_top i (by simp))

/-- Helper for Proposition 8.6: in the infinite branch, any coordinate value is bounded above by
the supremum of finite partial sums, so domain membership descends to each coordinate. -/
private theorem coordinate_dom_of_mem_dom_hilbertSumFunction_infinite
    (f : ∀ i, H i → EReal) [Infinite I] {x : lp H 2} (hx : x ∈ dom (hilbertSumFunction f)) :
    ∀ i, x i ∈ dom (f i) := by
  -- A singleton partial sum sits below the supremum, so no coordinate can equal `⊤`.
  intro i
  rw [mem_dom_iff]
  rw [mem_dom_iff] at hx
  have hsum_ne_top :
      sSup (Set.range fun J : Finset I ↦ J.sum (fun j ↦ f j (x j))) ≠ ⊤ := by
    simpa [hilbertSumFunction_apply_of_infinite (f := f) (x := x)] using ne_of_lt hx
  have hsingle :
      f i (x i) ≤ sSup (Set.range fun J : Finset I ↦ J.sum (fun j ↦ f j (x j))) := by
    -- The singleton partial sum is one of the terms under the supremum.
    simpa using
      (le_sSup (Set.mem_range_self ({i} : Finset I)) :
        ({i} : Finset I).sum (fun j ↦ f j (x j)) ≤
          sSup (Set.range fun J : Finset I ↦ J.sum (fun j ↦ f j (x j))))
  refine lt_top_iff_ne_top.mpr ?_
  intro htop
  have hsup_eq_top :
      sSup (Set.range fun J : Finset I ↦ J.sum (fun j ↦ f j (x j))) = ⊤ := by
    exact top_le_iff.mp (by simpa [htop] using hsingle)
  exact hsum_ne_top hsup_eq_top

/-- Helper for Proposition 8.6: the lower bound on `sInf (Set.range (f i))` implies every
coordinate value is nonnegative. -/
private theorem coordinate_nonneg_of_sInf_nonneg
    (f : ∀ i, H i → EReal) (hsInf : ∀ i, 0 ≤ sInf (Set.range (f i))) :
    ∀ i z, 0 ≤ f i z := by
  -- Each value lies above the infimum of the coordinate function range.
  intro i z
  exact le_trans (hsInf i) (sInf_le (Set.mem_range_self z))

/-- Helper for Proposition 8.6: every finite partial sum of the Hilbert-sum function satisfies the
coordinatewise Jensen inequality. -/
private theorem finite_partial_sum_jensen
    (f : ∀ i, H i → EReal) (hconv : ∀ i, Convex ℝ (epigraph (f i)))
    {x y : lp H 2} {α : ℝ} (hα : 0 < α) (hα_lt_one : α < 1) (J : Finset I)
    (hxdom : ∀ i ∈ J, x i ∈ dom (f i)) (hydom : ∀ i ∈ J, y i ∈ dom (f i)) :
    J.sum (fun i ↦ f i ((α • x + (1 - α) • y) i)) ≤
      (α : EReal) * J.sum (fun i ↦ f i (x i)) +
        (((1 - α : ℝ) : EReal) * J.sum (fun i ↦ f i (y i))) := by
  let αE : EReal := α
  let βE : EReal := (1 - α : ℝ)
  have hαE_nonneg : 0 ≤ αE := by
    exact EReal.coe_nonneg.mpr hα.le
  have hβE_nonneg : 0 ≤ βE := by
    exact EReal.coe_nonneg.mpr (sub_nonneg.mpr (le_of_lt hα_lt_one))
  have hαE_ne_top : αE ≠ ⊤ := EReal.coe_ne_top α
  have hβE_ne_top : βE ≠ ⊤ := EReal.coe_ne_top (1 - α)
  have hpointwise :
      ∀ i ∈ J,
        f i ((α • x + (1 - α) • y) i) ≤ αE * f i (x i) + βE * f i (y i) := by
    intro i hi
    -- Apply the Jensen characterization to the `i`th coordinate function.
    have hJ := (convex_epigraph_iff_jensen_on_dom_local (g := f i)).1 (hconv i)
    simpa [αE, βE, Pi.smul_apply, Pi.add_apply] using hJ (hxdom i hi) (hydom i hi) hα hα_lt_one
  calc
    J.sum (fun i ↦ f i ((α • x + (1 - α) • y) i))
        ≤ J.sum (fun i ↦ αE * f i (x i) + βE * f i (y i)) := by
          -- Sum the pointwise coordinate inequalities over the finite set `J`.
          exact Finset.sum_le_sum fun i hi ↦ hpointwise i hi
    _ = J.sum (fun i ↦ αE * f i (x i)) + J.sum (fun i ↦ βE * f i (y i)) := by
          rw [Finset.sum_add_distrib]
    _ = αE * J.sum (fun i ↦ f i (x i)) + βE * J.sum (fun i ↦ f i (y i)) := by
          -- Pull the two nonnegative finite scalars outside the finite sums.
          have hxsum :
              J.sum (fun i ↦ αE * f i (x i)) = αE * J.sum (fun i ↦ f i (x i)) := by
            symm
            exact
              mul_finset_sum_of_nonneg_of_ne_top αE hαE_nonneg hαE_ne_top J
                (fun i ↦ f i (x i))
          have hysum :
              J.sum (fun i ↦ βE * f i (y i)) = βE * J.sum (fun i ↦ f i (y i)) := by
            symm
            exact
              mul_finset_sum_of_nonneg_of_ne_top βE hβE_nonneg hβE_ne_top J
                (fun i ↦ f i (y i))
          rw [hxsum, hysum]
    _ = (α : EReal) * J.sum (fun i ↦ f i (x i)) +
          (((1 - α : ℝ) : EReal) * J.sum (fun i ↦ f i (y i))) := by
          simp [αE, βE]

-- Proof sketch: in the finite case, sum the coordinatewise convexity inequalities over all
-- indices. In the infinite case, use the lower bound `0 ≤ sInf (Set.range (f i))` to ensure every
-- finite partial sum is monotone in the index set, apply convexity to each finite partial sum, and
-- then take the supremum over all finite subsets.
/-- Proposition 8.6: if each coordinate function on a family of real Hilbert spaces has convex
epigraph, then the function on the Hilbert sum `lp H 2` obtained by summing the coordinate values
is convex provided either the index type is finite or every coordinate function is bounded below by
`0`. -/
theorem convex_epigraph_hilbertSumFunction
    (f : ∀ i, H i → EReal)
    (hnoBot : ∀ i x, f i x ≠ ⊥)
    (hconv : ∀ i, Convex ℝ (epigraph (f i)))
    (hfinite_or_nonneg : Finite I ∨ ∀ i, 0 ≤ sInf (Set.range (f i))) :
    Convex ℝ (epigraph (hilbertSumFunction f)) := by
  -- Route correction: the earlier counterexample disappears under `hnoBot`; we therefore prove
  -- convexity by a direct Jensen argument for `hilbertSumFunction` itself.
  refine (convex_epigraph_iff_jensen_on_dom_local (g := hilbertSumFunction f)).2 ?_
  intro x y hx hy α hα hα_lt_one
  by_cases hI : Finite I
  · let _ : Finite I := hI
    let _ : Fintype I := Fintype.ofFinite I
    have hxcoord := coordinate_dom_of_mem_dom_hilbertSumFunction_finite
      (f := f) hnoBot hx
    have hycoord := coordinate_dom_of_mem_dom_hilbertSumFunction_finite
      (f := f) hnoBot hy
    -- In the finite case, the Hilbert-sum function is the ordinary total sum.
    rw [hilbertSumFunction_apply_of_finite, hilbertSumFunction_apply_of_finite,
      hilbertSumFunction_apply_of_finite]
    simpa using
      (finite_partial_sum_jensen (f := f) (hconv := hconv) (x := x) (y := y)
        (hα := hα) (hα_lt_one := hα_lt_one) (J := Finset.univ)
        (fun i _ ↦ hxcoord i) (fun i _ ↦ hycoord i))
  · have hnonneg : ∀ i, 0 ≤ sInf (Set.range (f i)) := by
      rcases hfinite_or_nonneg with hfinite | hnonneg
      · exact (hI hfinite).elim
      · exact hnonneg
    have _ : Infinite I := (not_finite_iff_infinite.mp hI)
    have hxcoord := coordinate_dom_of_mem_dom_hilbertSumFunction_infinite
      (f := f) hx
    have hycoord := coordinate_dom_of_mem_dom_hilbertSumFunction_infinite
      (f := f) hy
    have hcoord_nonneg := coordinate_nonneg_of_sInf_nonneg (f := f) hnonneg
    -- In the infinite case, compare each finite partial sum with the corresponding supremum.
    rw [hilbertSumFunction_apply_of_infinite, hilbertSumFunction_apply_of_infinite,
      hilbertSumFunction_apply_of_infinite]
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨J, rfl⟩
    have hpartial :
        J.sum (fun i ↦ f i ((α • x + (1 - α) • y) i)) ≤
          (α : EReal) * J.sum (fun i ↦ f i (x i)) +
            (((1 - α : ℝ) : EReal) * J.sum (fun i ↦ f i (y i))) :=
      finite_partial_sum_jensen (f := f) (hconv := hconv) (x := x) (y := y)
        (hα := hα) (hα_lt_one := hα_lt_one) (J := J)
        (fun i hi ↦ hxcoord i) (fun i hi ↦ hycoord i)
    have hxpartial_le :
        J.sum (fun i ↦ f i (x i)) ≤
          sSup (Set.range fun K : Finset I ↦ K.sum (fun i ↦ f i (x i))) := by
      -- Every finite partial sum is bounded above by the supremum over all finite subsets.
      exact le_sSup (Set.mem_range_self J)
    have hypartial_le :
        J.sum (fun i ↦ f i (y i)) ≤
          sSup (Set.range fun K : Finset I ↦ K.sum (fun i ↦ f i (y i))) := by
      -- The same supremum bound holds at the second endpoint.
      exact le_sSup (Set.mem_range_self J)
    have hα_mul :
        (α : EReal) * J.sum (fun i ↦ f i (x i)) ≤
          (α : EReal) * sSup (Set.range fun K : Finset I ↦ K.sum (fun i ↦ f i (x i))) := by
      -- Multiply the partial-sum bound by the nonnegative coefficient `α`.
      exact mul_le_mul_of_nonneg_left hxpartial_le (EReal.coe_nonneg.mpr hα.le)
    have hβ_mul :
        (((1 - α : ℝ) : EReal) * J.sum (fun i ↦ f i (y i))) ≤
          (((1 - α : ℝ) : EReal) *
            sSup (Set.range fun K : Finset I ↦ K.sum (fun i ↦ f i (y i)))) := by
      -- The second coefficient `1 - α` is also nonnegative.
      exact mul_le_mul_of_nonneg_left hypartial_le
        (EReal.coe_nonneg.mpr (sub_nonneg.mpr (le_of_lt hα_lt_one)))
    have hrhs_le :
        (α : EReal) * J.sum (fun i ↦ f i (x i)) +
          (((1 - α : ℝ) : EReal) * J.sum (fun i ↦ f i (y i))) ≤
            (α : EReal) * sSup (Set.range fun K : Finset I ↦ K.sum (fun i ↦ f i (x i))) +
              (((1 - α : ℝ) : EReal) *
                sSup (Set.range fun K : Finset I ↦ K.sum (fun i ↦ f i (y i)))) :=
      add_le_add hα_mul hβ_mul
    exact le_trans hpartial hrhs_le

end ERealFunction
