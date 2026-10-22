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

variable {E : Type u}

/- Lemma 5.20 is `source-facing` for the Chapter 5 owner
`is_strongly_convex_function`. The perturbation hypothesis should reuse the Chapter 2 convexity
owner `is_convex_function`; the explicit source codomain condition `g : E → (-∞, ∞]` remains a
separate hypothesis `hg_ne_bot` because the ambient codomain is still `EReal`. The lower-level
`ConvexOn` formulation of `x ↦ (g x).toReal` on `effective_domain g` is a `bridge/view`
companion, not the main public entry. -/

-- Proof sketch: use `hf.ne_bot` together with `hg_ne_bot` to rule out `-∞` for `f + g`, read
-- convexity of `effective_domain g` from the set component of `hg`, combine it with
-- `hf.convex_effective_domain` to control the domain of `f + g`, and then add the strong-convex
-- Jensen inequality for `f` to the convex Jensen inequality for the real-valued restriction of
-- `g`, coercing back to `EReal`.
-- Bridge companion for Lemma 5.20: the perturbation term may be supplied through convexity of
-- the finite-valued restriction `x ↦ (g x).toReal` on `effective_domain g`, together with the
-- explicit hypothesis that `g` never takes the value `-∞`.
/-- Helper for Lemma 5.20: excluding `⊥` for both summands identifies the finite domain of
`x ↦ f x + g x` with the intersection of the finite domains of `f` and `g`. -/
private theorem effective_domain_add_eq_inter
    {f g : E → EReal} (hf_ne_bot : ∀ x, f x ≠ ⊥) (hg_ne_bot : ∀ x, g x ≠ ⊥) :
    effective_domain (fun x ↦ f x + g x) = effective_domain f ∩ effective_domain g := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · refine mem_effective_domain.mpr ?_
      by_contra hfx
      have hfx_top : f x = ⊤ := le_antisymm le_top (not_lt.mp hfx)
      have hsum_top : f x + g x = ⊤ := by
        simpa [hfx_top] using EReal.top_add_of_ne_bot (hg_ne_bot x)
      exact (ne_of_lt (mem_effective_domain.mp hx)) hsum_top
    · refine mem_effective_domain.mpr ?_
      by_contra hgx
      have hgx_top : g x = ⊤ := le_antisymm le_top (not_lt.mp hgx)
      have hsum_top : f x + g x = ⊤ := by
        simpa [hgx_top] using EReal.add_top_of_ne_bot (hf_ne_bot x)
      exact (ne_of_lt (mem_effective_domain.mp hx)) hsum_top
  · rintro ⟨hx, hy⟩
    -- Finite summands have a finite sum in `EReal`.
    exact mem_effective_domain.mpr <|
      EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hx))
        (ne_of_lt (mem_effective_domain.mp hy))

/-- Helper for Lemma 5.20: on the effective domain of `f + g`, `toReal` splits the sum into the
sum of the finite `toReal` values of `f` and `g`. -/
private theorem toReal_add_eq_of_mem_effective_domain_add
    {f g : E → EReal} (hf_ne_bot : ∀ x, f x ≠ ⊥) (hg_ne_bot : ∀ x, g x ≠ ⊥)
    {x : E} (hx : x ∈ effective_domain (fun z ↦ f z + g z)) :
    (f x + g x).toReal = (f x).toReal + (g x).toReal := by
  have hx_fg : x ∈ effective_domain f ∩ effective_domain g := by
    simpa [effective_domain_add_eq_inter hf_ne_bot hg_ne_bot] using hx
  rcases hx_fg with ⟨hx_f, hx_g⟩
  -- Membership in the effective domains excludes `⊤`, while the hypotheses exclude `⊥`.
  exact
    EReal.toReal_add (ne_of_lt (mem_effective_domain.mp hx_f)) (hf_ne_bot x)
      (ne_of_lt (mem_effective_domain.mp hx_g)) (hg_ne_bot x)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lemma 5.20: if `f` is `σ`-strongly convex and the finite-valued restriction
`x ↦ (g x).toReal` is convex on `effective_domain g`, with `g` never equal to `⊥`, then `f + g`
is `σ`-strongly convex. -/
theorem is_strongly_convex_function_add_of_convexOn_toReal
    {f g : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (hg_ne_bot : ∀ x, g x ≠ ⊥)
    (hg : ConvexOn ℝ (effective_domain g) (fun x ↦ (g x).toReal)) :
    is_strongly_convex_function (fun x ↦ f x + g x) σ := by
  let s : Set E := effective_domain (fun z ↦ f z + g z)
  have hdom_eq : s = effective_domain f ∩ effective_domain g := by
    simpa [s] using effective_domain_add_eq_inter hf.ne_bot hg_ne_bot
  refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
  refine ⟨hf.sigma_pos, ?_, ?_⟩
  · intro x
    -- The sum never takes the value `⊥` because neither summand does.
    exact EReal.add_ne_bot_iff.mpr ⟨hf.ne_bot x, hg_ne_bot x⟩
  · change StrongConvexOn s σ (fun x ↦ (f x + g x).toReal)
    change UniformConvexOn s (fun r ↦ σ / (2 : ℝ) * r ^ 2) (fun x ↦ (f x + g x).toReal)
    refine ⟨?_, ?_⟩
    · -- The common effective domain is the intersection of the two convex effective domains.
      rw [hdom_eq]
      exact hf.convex_effective_domain.inter hg.1
    · intro x hx y hy a b ha hb hab
      let z : E := a • x + b • y
      have hx_fg : x ∈ effective_domain f ∩ effective_domain g := by
        simpa [hdom_eq, s] using hx
      have hy_fg : y ∈ effective_domain f ∩ effective_domain g := by
        simpa [hdom_eq, s] using hy
      rcases hx_fg with ⟨hx_f, hx_g⟩
      rcases hy_fg with ⟨hy_f, hy_g⟩
      have hstrong_f := strongConvexOn_toReal_of_is_strongly_convex_function hf
      have hz_f : z ∈ effective_domain f := by
        exact hf.convex_effective_domain hx_f hy_f ha hb hab
      have hz_g : z ∈ effective_domain g := by
        exact hg.1 hx_g hy_g ha hb hab
      have hz_sum : z ∈ s := by
        simpa [hdom_eq, s, z] using And.intro hz_f hz_g
      have hf_real :
          (f z).toReal ≤
            a * (f x).toReal + b * (f y).toReal -
              ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ) := by
        -- Reuse the real-valued owner exposed by `hf` on `effective_domain f`.
        simpa [StrongConvexOn, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, z] using
          hstrong_f.2 hx_f hy_f ha hb hab
      have hg_real :
          (g z).toReal ≤ a * (g x).toReal + b * (g y).toReal := by
        exact hg.2 hx_g hy_g ha hb hab
      have hz_toReal :
          (f z + g z).toReal = (f z).toReal + (g z).toReal :=
        toReal_add_eq_of_mem_effective_domain_add hf.ne_bot hg_ne_bot hz_sum
      have hx_toReal :
          (f x + g x).toReal = (f x).toReal + (g x).toReal :=
        toReal_add_eq_of_mem_effective_domain_add hf.ne_bot hg_ne_bot hx
      have hy_toReal :
          (f y + g y).toReal = (f y).toReal + (g y).toReal :=
        toReal_add_eq_of_mem_effective_domain_add hf.ne_bot hg_ne_bot hy
      have hsum_real :
          (f z).toReal + (g z).toReal ≤
            (a * (f x).toReal + b * (f y).toReal -
                ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ)) +
              (a * (g x).toReal + b * (g y).toReal) :=
        add_le_add hf_real hg_real
      have hrewrite :
          (a * (f x).toReal + b * (f y).toReal -
              ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ)) +
            (a * (g x).toReal + b * (g y).toReal) =
          a * (f x + g x).toReal + b * (f y + g y).toReal -
            ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ) := by
        rw [hx_toReal, hy_toReal]
        ring
      -- Add the real-valued inequalities for `f` and `g`, then rewrite through `toReal_add`.
      have hfinal :
          (f z + g z).toReal ≤
            a * (f x + g x).toReal + b * (f y + g y).toReal -
              ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ) := by
        calc
        (f z + g z).toReal = (f z).toReal + (g z).toReal := hz_toReal
        _ ≤
            (a * (f x).toReal + b * (f y).toReal -
                ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ)) +
              (a * (g x).toReal + b * (g y).toReal) := hsum_real
        _ = a * (f x + g x).toReal + b * (f y + g y).toReal -
              ((σ / 2) * a * b * ‖x - y‖ ^ (2 : ℕ) : ℝ) := hrewrite
      simpa [z, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- Companion wrapper for Lemma 5.20: the Chapter 2 owner `is_convex_function g` supplies the
`ConvexOn` hypothesis on `x ↦ (g x).toReal`, so the bridge theorem above yields the source-facing
perturbation statement. -/
theorem is_strongly_convex_function_add_of_is_convex_function
    {f g : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (hg : is_convex_function g) (hg_ne_bot : ∀ x, g x ≠ ⊥) :
    is_strongly_convex_function (fun x ↦ f x + g x) σ := by
  refine is_strongly_convex_function_add_of_convexOn_toReal hf hg_ne_bot ?_
  exact convexOn_toReal_of_is_convex_function hg (fun x _ ↦ hg_ne_bot x)

end
