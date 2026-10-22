/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

namespace ERealFunction

/-- Helper for Proposition 8.18: convexity of a real-height epigraph transfers endpoint height
bounds to the corresponding convex combination. -/
private lemma combo_value_le_of_convex_epigraph
    (g : X → EReal) (hconv : Convex ℝ (epigraph g)) {x y : X} {ξ η a b : ℝ}
    (hx : g x ≤ (ξ : EReal)) (hy : g y ≤ (η : EReal))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    g (a • x + b • y) ≤ ((a * ξ + b * η : ℝ) : EReal) := by
  have hx_mem : (x, ξ) ∈ epigraph g := by
    -- The left endpoint belongs to the real-height epigraph at height `ξ`.
    simpa [mem_epigraph_iff] using hx
  have hy_mem : (y, η) ∈ epigraph g := by
    -- The right endpoint belongs to the real-height epigraph at height `η`.
    simpa [mem_epigraph_iff] using hy
  have hcombo_mem :
      (a • (x, ξ) + b • (y, η)) ∈ epigraph g := by
    -- Convexity of the epigraph propagates the two endpoint memberships to the barycenter.
    exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem ha hb hab
  rw [mem_epigraph_iff] at hcombo_mem
  -- Unfold the product scalar action to read the second coordinate as `a * ξ + b * η`.
  simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem

omit [AddCommMonoid X] [Module ℝ X] in
/-- Helper for Proposition 8.18: a strict real height above the limit value yields eventual
membership in the corresponding approximating epigraphs. -/
private lemma eventually_mem_epigraph_of_tendsto_lt_height
    (fSeq : ℕ → X → EReal) (f : X → EReal) {x : X} {ξ : ℝ}
    (hlim : Filter.Tendsto (fun n ↦ fSeq n x) Filter.atTop (nhds (f x)))
    (hx : f x < (ξ : EReal)) :
    ∀ᶠ n in Filter.atTop, (x, ξ) ∈ epigraph (fSeq n) := by
  have hle :
      ∀ᶠ n in Filter.atTop, fSeq n x ≤ (ξ : EReal) :=
    hlim.eventually (Iic_mem_nhds hx)
  -- Eventual membership in the closed half-line is exactly eventual epigraph membership.
  simpa [mem_epigraph_iff] using hle

/-- Helper for Proposition 8.18: once both endpoint values are strictly below chosen real heights,
the convexity of each approximating epigraph gives the corresponding eventual bound at the convex
combination point. -/
private lemma eventually_combo_le_of_perturbed_heights
    (fSeq : ℕ → X → EReal) (f : X → EReal)
    (hconv : ∀ n, Convex ℝ (epigraph (fSeq n)))
    (hlim : ∀ x, Filter.Tendsto (fun n ↦ fSeq n x) Filter.atTop (nhds (f x)))
    {x y : X} {ξ η a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : f x < (ξ : EReal)) (hy : f y < (η : EReal)) :
    ∀ᶠ n in Filter.atTop, fSeq n (a • x + b • y) ≤ ((a * ξ + b * η : ℝ) : EReal) := by
  have hx_mem :
      ∀ᶠ n in Filter.atTop, (x, ξ) ∈ epigraph (fSeq n) :=
    eventually_mem_epigraph_of_tendsto_lt_height fSeq f (hlim x) hx
  have hy_mem :
      ∀ᶠ n in Filter.atTop, (y, η) ∈ epigraph (fSeq n) :=
    eventually_mem_epigraph_of_tendsto_lt_height fSeq f (hlim y) hy
  filter_upwards [hx_mem, hy_mem] with n hxn hyn
  -- Apply the one-step epigraph convexity estimate at index `n`.
  exact combo_value_le_of_convex_epigraph (fSeq n) (hconv n)
    (by simpa [mem_epigraph_iff] using hxn)
    (by simpa [mem_epigraph_iff] using hyn)
    ha hb hab

-- Proof sketch: apply the convexity inequality for each `fSeq n` to `x`, `y`, and their convex
-- combination, then pass to the limit at these three evaluation points.
/-- Proposition 8.18: if a sequence of extended-real-valued functions has convex epigraphs and
converges pointwise, then the limit function also has a convex epigraph, hence is convex. -/
theorem convex_epigraph_of_pointwise_tendsto
    (fSeq : ℕ → X → EReal) (f : X → EReal)
    (hconv : ∀ n, Convex ℝ (epigraph (fSeq n)))
    (hlim : ∀ x, Filter.Tendsto (fun n ↦ fSeq n x) Filter.atTop (nhds (f x))) :
    Convex ℝ (epigraph f) := by
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, ξ⟩
  rcases q with ⟨y, η⟩
  rw [mem_epigraph_iff] at hp hq
  -- Follow the source proof: prove the target bound by testing against every real `z` above it.
  rw [mem_epigraph_iff]
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have hz_real : a * ξ + b * η < z := by
    exact EReal.coe_lt_coe_iff.mp hz
  let δ : ℝ := (z - (a * ξ + b * η)) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hx_lt : f x < ((ξ + δ : ℝ) : EReal) := by
    -- The perturbed left height is strictly above the limiting value `f x`.
    refine lt_of_le_of_lt hp ?_
    exact EReal.coe_lt_coe_iff.mpr (by linarith [hδ])
  have hy_lt : f y < ((η + δ : ℝ) : EReal) := by
    -- The perturbed right height is strictly above the limiting value `f y`.
    refine lt_of_le_of_lt hq ?_
    exact EReal.coe_lt_coe_iff.mpr (by linarith [hδ])
  have hevent_combo :
      ∀ᶠ n in Filter.atTop,
        fSeq n (a • x + b • y) ≤ ((a * (ξ + δ) + b * (η + δ) : ℝ) : EReal) :=
    eventually_combo_le_of_perturbed_heights fSeq f hconv hlim ha hb hab hx_lt hy_lt
  have hperturbed_lt : a * (ξ + δ) + b * (η + δ) < z := by
    have hrewrite :
        a * (ξ + δ) + b * (η + δ) = (a * ξ + b * η) + δ := by
      calc
        a * (ξ + δ) + b * (η + δ) = (a * ξ + b * η) + (a + b) * δ := by ring
        _ = (a * ξ + b * η) + δ := by rw [hab, one_mul]
    rw [hrewrite]
    dsimp [δ]
    linarith
  have hperturbed_le :
      (((a * (ξ + δ) + b * (η + δ) : ℝ) : EReal)) ≤ (z : EReal) := by
    exact EReal.coe_le_coe_iff.mpr (le_of_lt hperturbed_lt)
  have hevent_z :
      ∀ᶠ n in Filter.atTop, fSeq n (a • x + b • y) ≤ (z : EReal) :=
    hevent_combo.mono fun _ hn ↦ hn.trans hperturbed_le
  -- Passing to the limit preserves the eventual upper bound by the closedness of `(-∞, z]`.
  exact le_of_tendsto (hlim (a • x + b • y)) hevent_z

end ERealFunction
