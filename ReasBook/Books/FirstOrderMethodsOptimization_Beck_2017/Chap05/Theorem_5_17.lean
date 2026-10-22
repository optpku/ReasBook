/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 5.17 is a `bridge/view` item: it compares the source-facing strong-convexity owner
`is_strongly_convex_function` from Definition 5.16 with the source-facing convexity owner
`is_convex_function` from Chapter 2 after subtracting the quadratic correction
`x ↦ (σ / 2) ‖x‖²`. The Euclidean-space hypothesis is formalized by `InnerProductSpace ℝ E`,
which is exactly the structure needed for mathlib's canonical characterization
`strongConvexOn_iff_convex`. -/

-- Semantic recall: mathlib provides the real-valued owner theorem
-- `strongConvexOn_iff_convex`; this item keeps the chapter's extended-real-valued API as the
-- main statement by using the canonical owners from Chapter 2 and `Definition_5_16`.

/-- Bridge/view companion to Theorem 5.17: after passing to the real-valued restriction on
`effective_domain f`, source strong convexity is exactly convexity of the quadratic shift in
mathlib's canonical `ConvexOn` form. -/
theorem is_strongly_convex_function_iff_convexOn_toReal_sub_half_sigma_norm_sq
    (f : E → EReal) (σ : ℝ) (hσ : 0 < σ) (h_ne_bot : ∀ x, f x ≠ ⊥) :
    is_strongly_convex_function f σ ↔
      ConvexOn ℝ (effective_domain f)
        (fun x ↦ (f x).toReal - (σ / 2) * ‖x‖ ^ (2 : ℕ)) := by
  rw [is_strongly_convex_function_iff_strongConvexOn_toReal]
  constructor
  · rintro ⟨_, _, hf⟩
    simpa using (strongConvexOn_iff_convex.mp hf)
  · intro hf
    refine ⟨hσ, h_ne_bot, ?_⟩
    simpa using (strongConvexOn_iff_convex.mpr hf)

/-- Helper for Theorem 5.17: subtracting a finite real shift from an `EReal` value that is not
`⊥` still avoids `⊥`. -/
lemma sub_coe_neBot_of_neBot {a : EReal} {r : ℝ} (ha : a ≠ ⊥) :
    a - (r : EReal) ≠ ⊥ := by
  -- Case split on the source value; the `⊥` case is excluded by hypothesis and the remaining
  -- cases simplify to either `⊤` or a real coercion.
  cases a with
  | bot => contradiction
  | top =>
      simp
  | coe a =>
      rw [show ((a : EReal) - (r : EReal)) = (((a - r : ℝ) : EReal)) by
        simpa using (EReal.coe_sub a r).symm]
      exact EReal.coe_ne_bot _

/-- Helper for Theorem 5.17: subtracting a finite real-valued shift preserves the effective
domain of an extended-real-valued function that never takes the value `⊥`. -/
lemma effective_domain_sub_coe_eq
    (f : E → EReal) (q : E → ℝ) (h_ne_bot : ∀ x, f x ≠ ⊥) :
    effective_domain (fun x ↦ f x - ((q x : ℝ) : EReal)) = effective_domain f := by
  ext x
  rw [mem_effective_domain, mem_effective_domain]
  constructor
  · intro hx
    rw [lt_top_iff_ne_top]
    intro htop
    simpa [htop] using hx
  · intro hx
    rw [lt_top_iff_ne_top] at hx ⊢
    -- Rewrite the shifted value as a finite real coercion, so it is automatically different from
    -- `⊤`.
    have hfx :
        f x = (((f x).toReal : ℝ) : EReal) := by
      symm
      exact EReal.coe_toReal hx (h_ne_bot x)
    have hshift :
        f x - ((q x : ℝ) : EReal) = (((f x).toReal - q x : ℝ) : EReal) := by
      rw [hfx]
      simpa using (EReal.coe_sub (f x).toReal (q x)).symm
    rw [hshift]
    exact EReal.coe_ne_top _

/-- Helper for Theorem 5.17: on the effective domain, subtracting a finite real-valued shift
commutes with `EReal.toReal`. -/
lemma toReal_sub_coe_eq
    (f : E → EReal) (q : E → ℝ) (h_ne_bot : ∀ x, f x ≠ ⊥)
    {x : E} (hx : x ∈ effective_domain f) :
    (f x - ((q x : ℝ) : EReal)).toReal = (f x).toReal - q x := by
  have hx_ne_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
  -- The effective-domain hypothesis makes `f x` finite, so `EReal.toReal_sub` applies directly.
  simpa using
    (EReal.toReal_sub hx_ne_top (h_ne_bot x) (EReal.coe_ne_top _) (EReal.coe_ne_bot _))

/-- Theorem 5.17: on a Euclidean space, for `σ > 0` and `f : E → (-∞, ∞]`, an
extended-real-valued function is `σ`-strongly convex if and only if subtracting
`(σ / 2) ‖x‖²` yields a convex extended-real-valued function. -/
theorem is_strongly_convex_function_iff_sub_half_sigma_norm_sq_is_convex
    (f : E → EReal) (σ : ℝ) (hσ : 0 < σ) (h_ne_bot : ∀ x, f x ≠ ⊥) :
    is_strongly_convex_function f σ ↔
      is_convex_function
        (fun x ↦ f x - ((((σ / 2) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
  let q : E → ℝ := fun x ↦ (σ / 2) * ‖x‖ ^ (2 : ℕ)
  let g : E → EReal := fun x ↦ f x - ((q x : ℝ) : EReal)
  have hg_ne_bot : ∀ x ∈ effective_domain g, g x ≠ ⊥ := by
    intro x _hx
    -- The shift is finite, so the ambient no-`⊥` hypothesis on `f` passes directly to `g`.
    exact sub_coe_neBot_of_neBot (a := f x) (r := q x) (h_ne_bot x)
  rw [is_strongly_convex_function_iff_convexOn_toReal_sub_half_sigma_norm_sq
    (f := f) (σ := σ) hσ h_ne_bot]
  rw [is_convex_function_iff_convexOn_toReal (f := g) hg_ne_bot]
  rw [effective_domain_sub_coe_eq (f := f) (q := q) h_ne_bot]
  constructor
  · intro hf_convex
    -- Rewrite the shifted `toReal` expression back to the quadratic-corrected real-valued owner.
    refine hf_convex.congr ?_
    intro x hx
    simpa [g, q] using (toReal_sub_coe_eq (f := f) (q := q) h_ne_bot (x := x) hx).symm
  · intro hg_convex
    -- Use the same pointwise normalization in the reverse direction.
    refine hg_convex.congr ?_
    intro x hx
    simpa [g, q] using toReal_sub_coe_eq (f := f) (q := q) h_ne_bot (x := x) hx

end
