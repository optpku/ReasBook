/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

omit [AddCommMonoid H] [Module ℝ H] in
/-- Helper for Proposition 8.4: every point in the effective domain admits a real height lying
above the function value. -/
private lemma exists_real_ge_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, f x ≤ (ξ : EReal) := by
  -- Domain membership means that the value lies strictly below `+∞`, so a real separator exists.
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

omit [AddCommMonoid H] [Module ℝ H] in
/-- Helper for Proposition 8.4: a real-height epigraph point has base point in the effective
domain. -/
private lemma mem_dom_of_mem_epigraph (f : H → EReal) {x : H} {ξ : ℝ}
    (hξ : (x, ξ) ∈ epigraph f) : x ∈ dom f := by
  -- A real epigraph height gives a finite upper bound on `f x`.
  rw [mem_epigraph_iff] at hξ
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hξ (EReal.coe_lt_top ξ)

omit [AddCommMonoid H] [Module ℝ H] in
/-- Helper for Proposition 8.4: a finite-above and non-`⊥` value gives a canonical real epigraph
point via `toReal`. -/
private lemma mem_epigraph_toReal_of_mem_dom_of_ne_bot (f : H → EReal) {x : H} (hx : x ∈ dom f)
    (hbot : f x ≠ ⊥) : (x, (f x).toReal) ∈ epigraph f := by
  -- The `toReal` coordinate lies above `f x`; this is the non-`⊥` branch used in Jensen's proof.
  have htop : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  simp [mem_epigraph_iff, EReal.coe_toReal htop hbot]
/-- Helper for Proposition 8.4: if the left endpoint takes value `-∞`, convexity of the epigraph
forces every strict convex combination with a finite point to take value `-∞` as well. -/
private lemma combo_value_eq_bot_of_left_bot_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {x y : H} (hfx : f x = ⊥) (hy : y ∈ dom f) {α : ℝ}
    (hα : 0 < α) (hα_lt_one : α < 1) :
    f (α • x + (1 - α) • y) = ⊥ := by
  -- Route correction: the textbook's choice `(x, f x)` is not a real-height epigraph point when
  -- `f x = ⊥`, so we instead drive the convex-combination height below every prescribed real bound.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  rcases exists_real_ge_of_mem_dom f hy with ⟨ξ, hξ⟩
  let η : ℝ := (r - (1 - α) * ξ) / α - 1
  have hx_mem : (x, η) ∈ epigraph f := by
    -- Any real height lies above `-∞`.
    rw [mem_epigraph_iff, hfx]
    simp
  have hy_mem : (y, ξ) ∈ epigraph f := by
    -- The chosen witness `ξ` places the right endpoint in the epigraph.
    simpa [mem_epigraph_iff] using hξ
  have hβ : 0 < 1 - α := sub_pos.mpr hα_lt_one
  have hcombo_mem :
      (α • (x, η) + (1 - α) • (y, ξ)) ∈ epigraph f := by
    -- Convexity transfers the two epigraph points to their strict convex combination.
    exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem hα hβ (by ring)
  have hcombo_le :
      f (α • x + (1 - α) • y) ≤ ((α * η + (1 - α) * ξ : ℝ) : EReal) := by
    -- Rewrite the product-space combination into the desired first and second coordinates.
    rw [mem_epigraph_iff] at hcombo_mem
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
  have hη_eq : α * η + (1 - α) * ξ = r - α := by
    -- The definition of `η` was chosen exactly so that the combined height equals `r - α`.
    dsimp [η]
    field_simp [hα.ne']
    ring
  have hheight_lt : ((α * η + (1 - α) * ξ : ℝ) : EReal) < (r : EReal) := by
    -- Since `α > 0`, the combined height is strictly below the target bound `r`.
    rw [hη_eq]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hα)
  exact lt_of_le_of_lt hcombo_le hheight_lt

-- Proof sketch: use `convex_iff_forall_pos` on `epigraph f`. In the forward direction, split on
-- whether either endpoint value is `⊥`; the `⊥` branch uses the structural propagation lemma above,
-- while the finite branch uses the real heights `(f x).toReal` and `(f y).toReal`. In the reverse
-- direction, start from arbitrary real-height epigraph points, recover domain membership, and apply
-- the Jensen inequality on `dom f`.
/-- Proposition 8.4: the real-height epigraph of an extended-real-valued function is convex if and
only if Jensen's inequality holds for every two points of the effective domain `dom f = {x | f x <
⊤}` and every coefficient `α ∈ ]0,1[`. -/
theorem convex_epigraph_iff_jensen_on_dom (f : H → EReal) :
    Convex ℝ (epigraph f) ↔
      ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) ≤
          (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
  constructor
  · intro hconv x y hx hy α hα hα_lt_one
    by_cases hfx : f x = ⊥
    · -- If the left endpoint is `-∞`, convexity pushes the whole strict segment value down to `-∞`.
      have hcombo_bot :
          f (α • x + (1 - α) • y) = ⊥ :=
        combo_value_eq_bot_of_left_bot_of_convex_epigraph f hconv hfx hy hα hα_lt_one
      have hαE : 0 < (α : EReal) := by
        exact EReal.coe_pos.mpr hα
      simp [hcombo_bot, hfx, EReal.mul_bot_of_pos hαE]
    · by_cases hfy : f y = ⊥
      · -- The right-endpoint `-∞` case is reduced to the left-endpoint lemma by symmetry.
        have hcombo_bot_swapped :
            f ((1 - α) • y + (1 - (1 - α)) • x) = ⊥ :=
          combo_value_eq_bot_of_left_bot_of_convex_epigraph f hconv hfy hx
            (sub_pos.mpr hα_lt_one) (by linarith)
        have hrewrite : 1 - (1 - α) = α := by ring
        have hcombo_bot :
            f (α • x + (1 - α) • y) = ⊥ := by
          simpa [hrewrite, add_comm, add_left_comm, add_assoc] using hcombo_bot_swapped
        have hβE : 0 < ((1 - α : ℝ) : EReal) := by
          exact EReal.coe_pos.mpr (sub_pos.mpr hα_lt_one)
        simp [hcombo_bot, hfy]
      · -- When both endpoint values are genuine real heights, the textbook `toReal` argument applies.
        have hx_mem : (x, (f x).toReal) ∈ epigraph f :=
          mem_epigraph_toReal_of_mem_dom_of_ne_bot f hx hfx
        have hy_mem : (y, (f y).toReal) ∈ epigraph f :=
          mem_epigraph_toReal_of_mem_dom_of_ne_bot f hy hfy
        have hβ : 0 < 1 - α := sub_pos.mpr hα_lt_one
        have hcombo_mem :
            (α • (x, (f x).toReal) + (1 - α) • (y, (f y).toReal)) ∈ epigraph f := by
          -- Convexity of the epigraph gives the combined real-height point.
          exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem hα hβ (by ring)
        have hcombo_le :
            f (α • x + (1 - α) • y) ≤
              ((α * (f x).toReal + (1 - α) * (f y).toReal : ℝ) : EReal) := by
          -- Expand the product-space convex combination into its two coordinates.
          rw [mem_epigraph_iff] at hcombo_mem
          simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
        have hxtop : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
        have hytop : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
        calc
          f (α • x + (1 - α) • y)
              ≤ ((α * (f x).toReal + (1 - α) * (f y).toReal : ℝ) : EReal) := hcombo_le
          _ = (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
            rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hxtop hfx,
              EReal.coe_toReal hytop hfy]
  · intro hJ
    refine (convex_iff_forall_pos).2 ?_
    intro p hp q hq a b ha hb hab
    rcases p with ⟨x, ξ⟩
    rcases q with ⟨y, η⟩
    have hx : x ∈ dom f := mem_dom_of_mem_epigraph f hp
    have hy : y ∈ dom f := mem_dom_of_mem_epigraph f hq
    have ha_lt_one : a < 1 := by nlinarith
    have hb_eq : b = 1 - a := by nlinarith
    have haE : 0 < (a : EReal) := EReal.coe_pos.mpr ha
    have hbE : 0 < (b : EReal) := EReal.coe_pos.mpr hb
    have hJxy :
        f (a • x + b • y) ≤ (a : EReal) * f x + ((b : EReal) * f y) := by
      -- Rewrite the Jensen coefficient `1 - a` using `a + b = 1`.
      simpa [hb_eq] using hJ hx hy ha ha_lt_one
    have hx_le :
        (a : EReal) * f x ≤ (a : EReal) * (ξ : EReal) :=
      mul_le_mul_of_nonneg_left ((mem_epigraph_iff f x ξ).mp hp) haE.le
    have hy_le :
        (b : EReal) * f y ≤ (b : EReal) * (η : EReal) :=
      mul_le_mul_of_nonneg_left ((mem_epigraph_iff f y η).mp hq) hbE.le
    have hsum_le :
        (a : EReal) * f x + (b : EReal) * f y ≤
          (a : EReal) * (ξ : EReal) + (b : EReal) * (η : EReal) :=
      add_le_add hx_le hy_le
    have hfinal :
        f (a • x + b • y) ≤ ((a * ξ + b * η : ℝ) : EReal) := by
      -- Compare the Jensen upper bound with the given epigraph heights.
      calc
        f (a • x + b • y)
            ≤ (a : EReal) * f x + (b : EReal) * f y := hJxy
        _ ≤ (a : EReal) * (ξ : EReal) + (b : EReal) * (η : EReal) := hsum_le
        _ = ((a * ξ + b * η : ℝ) : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    -- This is exactly the epigraph membership of the convex combination point.
    rw [mem_epigraph_iff]
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal

end ERealFunction
