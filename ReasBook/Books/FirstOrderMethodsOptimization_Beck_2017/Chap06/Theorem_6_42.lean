/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

recall strongDualSubdifferential

/- Theorem 6.42 sits in the proximal/subdifferential domain.

Domain sampling:
- `prox[f]` from Definition 6.1 is the source-facing Chapter 6 owner.
- `strongDualSubdifferential` from Chapter 3 is the canonical continuous-dual surface for
  extended-real subgradients.
- The primitive owner-level datum is therefore a pair of strong-dual subgradients
  `gᵤ ∈ strongDualSubdifferential f u` and `gᵥ ∈ strongDualSubdifferential f v`; the proximal
  vectors `toDualMap ℝ E (x - u)` and `toDualMap ℝ E (y - v)` are already a derived specialization
  of that owner surface.
- `prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential` from Theorem 6.39 is the
  canonical proper-convex bridge from singleton proximal points to that Chapter 3 surface.
- `metricProjection_firmly_nonexpansive` from Theorem 5.4 fixes the intended firm-nonexpansive
  statement shape.
- No upstream theorem already owns the specific monotonicity consequence needed here, so this file
  should expose that monotonicity first at the `strongDualSubdifferential` owner level and treat
  the singleton proximal hypotheses as derived source-facing API coming directly from the proximal
  minimizer owner `prox[f]`.

Layer triage:
- `core/canonical`: monotonicity for arbitrary strong-dual subgradients in
  `strongDualSubdifferential`.
- `source-facing`: the textbook singleton identities `prox[f] x = {u}` and `prox[f] y = {v}`.
- `bridge/view`: the `toDualMap` specialization below, together with Theorem 6.39 for the
  proper-convex bridge to Chapter 3; the final source-facing theorem carries the textbook
  proper/closed/convex assumptions so singleton proximal data is not used outside its valid
  convex-analysis setting. -/

section FirmlyNonexpansive

variable (f : E → EReal)

-- Proof sketch: apply the subgradient inequality defining `gᵤ ∈ ∂f(u)` to the point `v` and the
-- one defining `gᵥ ∈ ∂f(v)` to the point `u`. Adding the two inequalities gives
-- `(gᵤ - gᵥ) (u - v) ≥ 0`.
/-- Helper for Theorem 6.42: canonical monotonicity of the Chapter 3 owner
`strongDualSubdifferential` once the two function values are finite from below. -/
theorem strongDualSubdifferential_mono
    (u v : E) {gᵤ gᵥ : StrongDual ℝ E}
    (hu : gᵤ ∈ strongDualSubdifferential f u)
    (hv : gᵥ ∈ strongDualSubdifferential f v)
    (hfu_bot : f u ≠ ⊥) (hfv_bot : f v ≠ ⊥) :
    0 ≤ (gᵤ - gᵥ) (u - v) := by
  -- Route correction: without excluding `⊥`, the project's Chapter 3 subgradient predicate is too
  -- weak for monotonicity, since `f u = ⊥` makes every linear functional a subgradient at `u`.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain] at hu hv
  rcases hu with ⟨hu_eff, hsub_u⟩
  rcases hv with ⟨hv_eff, hsub_v⟩
  have hu_val :
      f u = (((f u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne hfu_bot).symm
  have hv_val :
      f v = (((f v).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hv_eff).ne hfv_bot).symm
  -- Convert the two subgradient inequalities to real inequalities at the opposite base points.
  have huv_real : (f u).toReal + gᵤ (v - u) ≤ (f v).toReal := by
    have huv := hsub_u v hv_eff
    rw [hu_val, hv_val] at huv
    have huv' :
        ((((f u).toReal + gᵤ (v - u) : ℝ)) : EReal) ≤ (((f v).toReal : ℝ) : EReal) := by
      simpa [ge_iff_le, EReal.coe_add, add_comm, add_left_comm, add_assoc] using huv
    exact EReal.coe_le_coe_iff.mp huv'
  have hvu_real : (f v).toReal + gᵥ (u - v) ≤ (f u).toReal := by
    have hvu := hsub_v u hu_eff
    rw [hv_val, hu_val] at hvu
    have hvu' :
        ((((f v).toReal + gᵥ (u - v) : ℝ)) : EReal) ≤ (((f u).toReal : ℝ) : EReal) := by
      simpa [ge_iff_le, EReal.coe_add, add_comm, add_left_comm, add_assoc] using hvu
    exact EReal.coe_le_coe_iff.mp hvu'
  have hsum : gᵤ (v - u) + gᵥ (u - v) ≤ 0 := by
    linarith
  have hgᵤ_neg : gᵤ (v - u) = -gᵤ (u - v) := by
    have hneg : v - u = -(u - v) := by
      abel
    rw [hneg, map_neg]
  -- Re-express the dual difference on `u - v` in the monotone form obtained above.
  have hgoal_eq : (gᵤ - gᵥ) (u - v) = -(gᵤ (v - u) + gᵥ (u - v)) := by
    change gᵤ (u - v) - gᵥ (u - v) = -(gᵤ (v - u) + gᵥ (u - v))
    rw [hgᵤ_neg]
    ring
  have hgoal_nonneg : 0 ≤ -(gᵤ (v - u) + gᵥ (u - v)) := by
    linarith
  simpa [hgoal_eq] using hgoal_nonneg

-- Proof sketch: specialize `strongDualSubdifferential_mono` to
-- `gᵤ = toDualMap ℝ E (x - u)` and `gᵥ = toDualMap ℝ E (y - v)`, then rewrite the dual pairings
-- with the inner product and expand the resulting algebraic identity to obtain
-- `⟪x - y, u - v⟫ ≥ ‖u - v‖²`.
/-- Helper for Theorem 6.42: firm nonexpansiveness specialized to the proximal strong-dual data
`toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u` and
`toDualMap ℝ E (y - v) ∈ strongDualSubdifferential f v`. The singleton proximal formulation of
Theorem 6.42 is derived from this bridge theorem through Theorem 6.39. -/
theorem toDualMap_sub_mem_strongDualSubdifferential_firmly_nonexpansive
    (x y u v : E)
    (hx : toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u)
    (hy : toDualMap ℝ E (y - v) ∈ strongDualSubdifferential f v)
    (hfu_bot : f u ≠ ⊥) (hfv_bot : f v ≠ ⊥) :
    inner ℝ (x - y) (u - v) ≥ ‖u - v‖ ^ (2 : ℕ) := by
  -- First apply the owner-level monotonicity theorem to the two Riesz representatives.
  have hmono :=
    strongDualSubdifferential_mono (f := f) u v hx hy hfu_bot hfv_bot
  -- Then rewrite the dual pairing as the desired inner-product expression.
  have hrewrite :
      (toDualMap ℝ E (x - u) - toDualMap ℝ E (y - v)) (u - v) =
        inner ℝ (x - y) (u - v) - ‖u - v‖ ^ (2 : ℕ) := by
    change inner ℝ (x - u) (u - v) - inner ℝ (y - v) (u - v) =
      inner ℝ (x - y) (u - v) - ‖u - v‖ ^ (2 : ℕ)
    rw [inner_sub_left, inner_sub_left, inner_sub_left]
    have huv :
        inner ℝ u (u - v) - inner ℝ v (u - v) = ‖u - v‖ ^ (2 : ℕ) := by
      calc
        inner ℝ u (u - v) - inner ℝ v (u - v) = inner ℝ (u - v) (u - v) := by
          rw [← inner_sub_left]
        _ = ‖u - v‖ ^ (2 : ℕ) := by
          rw [real_inner_self_eq_norm_sq]
    linarith
  have hgoal : 0 ≤ inner ℝ (x - y) (u - v) - ‖u - v‖ ^ (2 : ℕ) := by
    rw [← hrewrite]
    exact hmono
  linarith

-- Proof sketch: rewrite `hx` and `hy` via `mem_proximal_mapping_iff` to obtain the two proximal
-- minimizer inequalities
-- `proximal_objective f x u ≤ proximal_objective f x v` and
-- `proximal_objective f y v ≤ proximal_objective f y u`. Expand both objectives, add the
-- inequalities, and rearrange the quadratic terms to obtain
-- `⟪x - y, u - v⟫ ≥ ‖u - v‖²`.
/-- Theorem 6.42: (a) firm nonexpansivity of proximal points for a proper closed convex
extended-real-valued function. If `u` and `v` are the unique proximal points of `f` at `x` and
`y`, then `⟪x - y, u - v⟫ ≥ ‖u - v‖²`. -/
theorem prox_eq_singleton_firmly_nonexpansive
    (x y u v : E)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    (hx : prox[f] x = {u}) (hy : prox[f] y = {v}) :
    inner ℝ (x - y) (u - v) ≥ ‖u - v‖ ^ (2 : ℕ) := by
  -- The source theorem needs the original proper/closed/convex hypotheses; singleton proximal
  -- data alone is not enough outside the convex setting.
  let _ := hf_closed
  -- Convert the singleton proximal identities into the canonical strong-dual subgradients.
  have hx_sub :
      toDualMap ℝ E (x - u) ∈ strongDualSubdifferential f u := by
    exact
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        f hf_proper hf_convex x u).mp hx
  have hy_sub :
      toDualMap ℝ E (y - v) ∈ strongDualSubdifferential f v := by
    exact
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        f hf_proper hf_convex y v).mp hy
  -- Feed the two residual subgradients into the owner-level firm nonexpansive inequality.
  exact
    toDualMap_sub_mem_strongDualSubdifferential_firmly_nonexpansive
      (f := f) x y u v hx_sub hy_sub (hf_proper.ne_bot u) (hf_proper.ne_bot v)

-- Proof sketch: apply `prox_eq_singleton_firmly_nonexpansive` and then use the Cauchy--Schwarz
-- inequality to bound `⟪x - y, u - v⟫` by `‖x - y‖ * ‖u - v‖`. If `u = v`, the claim is
-- immediate; otherwise divide by `‖u - v‖`.
/-- Nonexpansivity of proximal points for a proper closed convex extended-real-valued function:
under the same hypotheses as the firm nonexpansive inequality, the distance between the proximal
points is at most the distance between the base points. -/
theorem prox_eq_singleton_nonexpansive
    (x y u v : E)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    (hx : prox[f] x = {u}) (hy : prox[f] y = {v}) :
    ‖u - v‖ ≤ ‖x - y‖ := by
  -- Apply `prox_eq_singleton_firmly_nonexpansive` under the same textbook hypotheses and then use
  -- `real_inner_le_norm`.
  have hfirm :=
    prox_eq_singleton_firmly_nonexpansive
      (f := f) x y u v hf_proper hf_closed hf_convex hx hy
  -- Bound the firm inner product by Cauchy--Schwarz to reach a scalar inequality.
  have hcs : inner ℝ (x - y) (u - v) ≤ ‖x - y‖ * ‖u - v‖ := by
    exact real_inner_le_norm (x - y) (u - v)
  have hbound : ‖u - v‖ ^ (2 : ℕ) ≤ ‖x - y‖ * ‖u - v‖ := by
    linarith
  -- Normalize the square and conclude using nonnegativity of norms.
  rw [pow_two] at hbound
  nlinarith [hbound, norm_nonneg (u - v), norm_nonneg (x - y)]

end FirmlyNonexpansive

end
