/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Filter
open scoped Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Domain sampling for Proposition 14.3:
- `subdifferential` is the Chapter 3 `core/canonical` owner for the subgradient set `∂ h(x)`;
- `strongDualSubdifferential` is the topologized `bridge/view` needed only for the convergence of
  the sequence `a : ℕ → StrongDual ℝ E`;
- `is_subgradient_at_iff_forall_mem_effective_domain` is the primitive pointwise inequality API.

This proposition is `source-facing`: it says the graph of the subdifferential is sequentially
closed under strong-dual/space convergence. The public theorem surface should therefore use the
strong-dual bridge notation `∂ₛ h(x)` rather than the long raw owner name
`strongDualSubdifferential`, while the algebraic owner remains `∂ h(x)`. The textbook properness
and convexity hypotheses are redundant here: once `aₖ ∈ ∂ₛ h(bₖ)` is given,
lower semicontinuity is the only active assumption for passing to the limit. -/

recall subdifferential
recall strongDualSubdifferential

-- Proof sketch: fix any `z : E`. From `a k ∈ ∂ₛ h(b k)` we have
-- `h z ≥ h (b k) + a k (z - b k)` for every `k`. The map `(g, x) ↦ g x` is continuous on
-- `StrongDual ℝ E × E`, so `a k (z - b k) → aBar (z - bBar)`. Lower semicontinuity gives
-- `h bBar ≤ liminf h (b k)`, hence passing to the limit yields
-- `h z ≥ h bBar + aBar (z - bBar)` for all `z`, which is exactly `aBar ∈ ∂ₛ h(bBar)`.
/-- Helper for Proposition 14.3: lower semicontinuity bounds the value at the limit point by the
`liminf` along any convergent sequence. -/
private lemma lowerSemicontinuous_value_le_liminf_along_sequence
    (h : E → EReal) (hclosed : LowerSemicontinuous h) {b : ℕ → E} {bBar : E}
    (hb : Tendsto b atTop (𝓝 bBar)) :
    h bBar ≤ Filter.liminf (fun k ↦ h (b k)) atTop := by
  -- Compare the neighborhood-filter liminf at `bBar` with the mapped sequence filter.
  calc
    h bBar ≤ Filter.liminf h (𝓝 bBar) := hclosed.le_liminf bBar
    _ ≤ Filter.liminf h (Filter.map b atTop) := Filter.liminf_le_liminf_of_le hb
    _ = Filter.liminf (fun k ↦ h (b k)) atTop := by
      rw [← Filter.liminf_comp]
      rfl

/-- Helper for Proposition 14.3: the dual pairing term appearing in the subgradient inequality
converges in `EReal` along the limiting subgradient and base-point sequences. -/
lemma tendsto_subgradient_pairing_ereal
    (a : ℕ → StrongDual ℝ E) (b : ℕ → E) {aBar : StrongDual ℝ E} {bBar z : E}
    (ha : Tendsto a atTop (𝓝 aBar)) (hb : Tendsto b atTop (𝓝 bBar)) :
    Tendsto (fun k ↦ (((a k) (z - b k) : ℝ) : EReal)) atTop
      (𝓝 (((aBar (z - bBar) : ℝ) : EReal))) := by
  -- First pass to the real pairing by joint continuity of evaluation.
  have hdiff : Tendsto (fun k ↦ z - b k) atTop (𝓝 (z - bBar)) := tendsto_const_nhds.sub hb
  have hpair_real : Tendsto (fun k ↦ (a k) (z - b k)) atTop (𝓝 (aBar (z - bBar))) := by
    have hcont : Continuous (fun p : StrongDual ℝ E × E ↦ p.1 p.2) := by
      exact continuous_fst.clm_apply continuous_snd
    have hprod : Tendsto (fun k ↦ (a k, z - b k)) atTop (𝓝 (aBar, z - bBar)) := by
      exact ha.prodMk_nhds hdiff
    exact (hcont.tendsto (aBar, z - bBar)).comp hprod
  -- Then transport the real limit through the continuous coercion `ℝ → EReal`.
  exact (continuous_coe_real_ereal.tendsto _).comp hpair_real

/-- Helper for Proposition 14.3: strong-dual subgradient membership rewrites to the pointwise
support inequality on every point of the effective domain. -/
lemma pointwise_subgradient_bound_on_effective_domain
    (h : E → EReal) {x z : E} {g : StrongDual ℝ E}
    (hg : g ∈ ∂ₛ h(x)) (hz : z ∈ effective_domain h) :
    h x + (((g (z - x) : ℝ) : EReal)) ≤ h z := by
  -- Rewrite the strong-dual bridge back to the owner subgradient inequality.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain] at hg
  simpa [ge_iff_le] using hg.2 z hz

/-- Helper for Proposition 14.3: an eventual upper bound by a constant forces the `liminf`
to stay below that constant. -/
private lemma liminf_le_constant_of_eventually_le_ereal
    {u : ℕ → EReal} {c : EReal} (huc : ∀ᶠ k in atTop, u k ≤ c) :
    Filter.liminf u atTop ≤ c := by
  -- Any eventual lower bound for `u` can be compared to `c` on a common tail.
  exact Filter.liminf_le_of_le (f := atTop) (u := u) (a := c) (hf := by isBoundedDefault)
    fun b hb ↦ by
    rcases (hb.and huc).exists with ⟨k, hbk, hkc⟩
    exact le_trans hbk hkc

/-- Helper for Proposition 14.3: the limit support value is bounded below by the `liminf`
of the support sequence. -/
lemma limit_support_liminf_lower_bound
    (h : E → EReal) (hclosed : LowerSemicontinuous h) (a : ℕ → StrongDual ℝ E) (b : ℕ → E)
    {aBar : StrongDual ℝ E} {bBar z : E}
    (ha : Tendsto a atTop (𝓝 aBar))
    (hb : Tendsto b atTop (𝓝 bBar)) :
    h bBar + (((aBar (z - bBar) : ℝ) : EReal)) ≤
      Filter.liminf (fun k ↦ h (b k) + (((a k) (z - b k) : ℝ) : EReal)) atTop := by
  let v : ℕ → EReal := fun k ↦ (((a k) (z - b k) : ℝ) : EReal)
  have hh :
      h bBar ≤ Filter.liminf (fun k ↦ h (b k)) atTop :=
    lowerSemicontinuous_value_le_liminf_along_sequence h hclosed hb
  have hv :
      Tendsto v atTop (𝓝 (((aBar (z - bBar) : ℝ) : EReal))) :=
    tendsto_subgradient_pairing_ereal a b ha hb
  -- Pass the lower-semicontinuity bound and the pairing limit through `EReal.le_liminf_add`.
  calc
    h bBar + (((aBar (z - bBar) : ℝ) : EReal))
        = h bBar + Filter.liminf v atTop := by
            rw [hv.liminf_eq]
    _ ≤ Filter.liminf (fun k ↦ h (b k)) atTop + Filter.liminf v atTop := by
      exact add_le_add hh le_rfl
    _ ≤ Filter.liminf (fun k ↦ h (b k) + v k) atTop := by
      simpa [v] using
        (EReal.le_liminf_add (u := fun k ↦ h (b k)) (v := v) (f := atTop))

/-- Helper for Proposition 14.3: after passing the pointwise subgradient inequality to the limit,
the limit pair `(aBar, bBar)` still satisfies the supporting inequality at every point of the
effective domain. -/
lemma limit_subgradient_inequality_on_effective_domain
    (h : E → EReal) (hclosed : LowerSemicontinuous h) (a : ℕ → StrongDual ℝ E) (b : ℕ → E)
    {aBar : StrongDual ℝ E} {bBar z : E}
    (hsub : ∀ k : ℕ, a k ∈ ∂ₛ h(b k))
    (ha : Tendsto a atTop (𝓝 aBar))
    (hb : Tendsto b atTop (𝓝 bBar))
    (hz : z ∈ effective_domain h) :
    h bBar + (((aBar (z - bBar) : ℝ) : EReal)) ≤ h z := by
  let u : ℕ → EReal := fun k ↦ h (b k) + (((a k) (z - b k) : ℝ) : EReal)
  have hu_le : ∀ᶠ k in atTop, u k ≤ h z := by
    -- Apply the pointwise support bound at every sequence index.
    exact Eventually.of_forall fun k ↦
      pointwise_subgradient_bound_on_effective_domain h (hsub k) hz
  -- Route correction: the previous monolithic liminf proof timed out; split the lower-bound and
  -- eventual-upper-bound halves, then chain them in one short `calc`.
  calc
    h bBar + (((aBar (z - bBar) : ℝ) : EReal)) ≤ Filter.liminf u atTop := by
      simpa [u] using
        limit_support_liminf_lower_bound h hclosed a b ha hb (z := z)
    _ ≤ h z := liminf_le_constant_of_eventually_le_ereal hu_le

/-- Helper for Proposition 14.3: the limit base point still lies in the effective domain. -/
lemma limit_basepoint_mem_effective_domain
    (h : E → EReal) (hclosed : LowerSemicontinuous h) (a : ℕ → StrongDual ℝ E) (b : ℕ → E)
    {aBar : StrongDual ℝ E} {bBar : E}
    (hsub : ∀ k : ℕ, a k ∈ ∂ₛ h(b k))
    (ha : Tendsto a atTop (𝓝 aBar))
    (hb : Tendsto b atTop (𝓝 bBar)) :
    bBar ∈ effective_domain h := by
  have hsub0 := hsub 0
  -- The first subgradient witness already certifies finiteness at `b 0`.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain] at hsub0
  have hb0 : b 0 ∈ effective_domain h := hsub0.1
  -- Route correction: extract finiteness at the limit point via the staged support inequality
  -- instead of re-running the whole liminf argument inside the final theorem.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hbBar_top
  have hlimit :
      h bBar + (((aBar (b 0 - bBar) : ℝ) : EReal)) ≤ h (b 0) :=
    limit_subgradient_inequality_on_effective_domain h hclosed a b
      (z := b 0) hsub ha hb hb0
  rw [hbBar_top, EReal.top_add_coe] at hlimit
  have hb0_top : h (b 0) = ⊤ := le_antisymm le_top hlimit
  exact (mem_effective_domain.mp hb0).ne hb0_top

/-- Proposition 14.3: if each `a k` belongs to the subdifferential of a lower semicontinuous
extended-real-valued function `h` at `b k`, and `a k → aBar`, `b k → bBar`, then `aBar` belongs
to the subdifferential of `h` at `bBar`. The statement uses the strong-dual bridge notation
`∂ₛ h(x)`, so the theorem surface stays source-readable without exposing the long raw bridge name
`strongDualSubdifferential`. The textbook properness and convexity hypotheses are redundant for
this closed-graph property, so lower semicontinuity is the only public assumption. -/
theorem mem_strongDualSubdifferential_of_tendsto_subgradient_sequences
    (h : E → EReal) (hclosed : LowerSemicontinuous h) (a : ℕ → StrongDual ℝ E) (b : ℕ → E)
    {aBar : StrongDual ℝ E} {bBar : E}
    (hsub : ∀ k : ℕ, a k ∈ ∂ₛ h(b k))
    (ha : Tendsto a atTop (𝓝 aBar))
    (hb : Tendsto b atTop (𝓝 bBar)) :
    aBar ∈ ∂ₛ h(bBar) := by
  -- Package the staged limit inequality back into the Chapter 3 subgradient API.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨limit_basepoint_mem_effective_domain h hclosed a b hsub ha hb, ?_⟩
  intro z hz
  simpa [ge_iff_le] using
    limit_subgradient_inequality_on_effective_domain h hclosed a b
      (z := z) hsub ha hb hz

end
