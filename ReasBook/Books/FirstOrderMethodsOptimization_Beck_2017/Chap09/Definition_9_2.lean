/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 9.2 has two layers in the local API.
- `bregmanDistance` is a `bridge/view` owner in the Hilbert-space gradient setting, since its
  formula uses both `∇` and `inner`.
- The standing assumptions on `ω` over `C` are a `source-facing` Chapter 9 owner recorded below as
  `IsBregmanPotentialOn`; that owner itself lives in the weaker normed-space convex-analysis
  setting and the constrained-potential statement for `ω + δ_C` is derived from it. -/

/-- The Bregman-distance component of Definition 9.2: the Bregman distance associated with a
proper closed convex potential `ω`,
viewed as a totalized real-valued function with intended source domain
`dom(ω) × dom(∂ ω)`, is
`B_ω(x, y) = ω(x) - ω(y) - ⟪∇ω(y), x - y⟫` on finite points. -/
def bregmanDistance (ω : E → EReal) (x y : E) : ℝ :=
  (ω x).toReal - (ω y).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y)

notation "B[" ω "]" => bregmanDistance ω
notation "B[" ω "]" => bregmanDistance (Function.toEReal ω)

-- Proof sketch: unfold `bregmanDistance`; evaluating the definition at `(x, y)` gives the
-- displayed totalized real-valued expression.
/-- The defining formula for `bregmanDistance` at `(x, y)` is
`ω(x) - ω(y) - ⟪∇ω(y), x - y⟫` on finite points. -/
@[simp] theorem bregmanDistance_def (ω : E → EReal) (x y : E) :
    B[ω] x y =
      (ω x).toReal - (ω y).toReal - inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) := by
  -- Unfold the owner definition once; the displayed formula is definitional.
  rfl

-- Proof sketch: unfold `bregmanDistance` at `(x, x)`; the two function values cancel and the
-- remaining inner product is against `x - x = 0`.
/-- The Bregman distance of a point from itself is zero. -/
@[simp] theorem bregmanDistance_self_eq_zero (ω : E → EReal) (x : E) :
    B[ω] x x = 0 := by
  -- Rewrite the diagonal case to the explicit formula and simplify the zero displacement.
  rw [bregmanDistance_def]
  simp

-- Proof sketch: substitute `y = x` and reduce to `bregmanDistance_self_eq_zero`.
/-- If the two arguments coincide, then the Bregman distance vanishes. -/
theorem bregmanDistance_eq_zero_of_eq (ω : E → EReal) {x y : E} (hxy : x = y) :
    B[ω] x y = 0 := by
  -- Replace `y` by `x` and reuse the diagonal vanishing lemma.
  subst hxy
  simp

/-- For a real-valued potential, the Chapter 9 Bregman distance specializes to the textbook
formula `ω(x) - ω(y) - ⟪∇ω(y), x - y⟫`. -/
@[simp] theorem bregmanDistance_apply_real (ω : E → ℝ) (x y : E) :
    B[ω] x y = ω x - ω y - inner ℝ (∇ ω y) (x - y) := by
  simp [bregmanDistance, Function.toEReal]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Bregman potential on `C` with modulus `σ` is proper, closed, convex, differentiable on
`dom(∂ ω)`, contains `C` in `dom(ω)`, and has `ω.toReal` `σ`-strongly convex on `C`. The
equivalent constrained-potential formulation for `ω + δ_C` is derived below. -/
class IsBregmanPotentialOn (ω : E → EReal) (C : Set E) (σ : ℝ) : Prop
    extends IsProperExtendedRealFunction ω where
  closed : LowerSemicontinuous ω
  convex : is_convex_function ω
  differentiableOn_subdifferential_domain :
    DifferentiableOn ℝ (fun x ↦ (ω x).toReal) (subdifferential_domain ω)
  subset_effective_domain : C ⊆ effective_domain ω
  sigma_pos : 0 < σ
  strongConvexOn : StrongConvexOn C σ (fun x ↦ (ω x).toReal)

/-- Helper for Definition 9.2: for a Bregman potential on `C`, the constrained potential
`ω + δ_ C` has effective domain exactly `C`. -/
private theorem effectiveDomainAddIndicator_eq
    {ω : E → EReal} {C : Set E} {σ : ℝ} (hω : IsBregmanPotentialOn ω C σ) :
    effective_domain (ω + δ_ C) = C := by
  ext x
  constructor
  · intro hx
    -- Outside `C`, the indicator contributes `⊤`, so finiteness forces membership in `C`.
    by_cases hxC : x ∈ C
    · exact hxC
    · have hx_top : (ω + δ_ C) x = ⊤ := by
        simpa [Pi.add_apply, extendedIndicator_of_not_mem hxC] using
          EReal.add_top_of_ne_bot (hω.toIsProperExtendedRealFunction.ne_bot x)
      exact False.elim ((ne_of_lt (mem_effective_domain.mp hx)) hx_top)
  · intro hxC
    -- On `C`, the indicator vanishes, so the constrained effective domain matches that of `ω`.
    have hxω : x ∈ effective_domain ω := hω.subset_effective_domain hxC
    simpa [Pi.add_apply, extendedIndicator_of_mem hxC] using hxω

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Helper for Definition 9.2: on feasible points, the constrained potential `ω + δ_ C` has the
same real value as `ω`. -/
private theorem toRealAddIndicator_eqOn
    {ω : E → EReal} {C : Set E} :
    Set.EqOn (fun x ↦ ((ω + δ_ C) x).toReal) (fun x ↦ (ω x).toReal) C := by
  intro x hxC
  -- On `C`, the indicator term is zero, so the `toReal` value simplifies immediately.
  simp [Pi.add_apply, extendedIndicator_of_mem hxC]

-- Proof sketch: because `hω.subset_effective_domain` forces `ω` to be finite on `C`, the
-- constrained potential `ω + δ_C` has effective domain exactly `C`, and on that set its
-- real-valued restriction agrees with `x ↦ (ω x).toReal`; the claim is therefore just the stored
-- `hω.strongConvexOn` rewritten through the canonical constrained-potential view.
/-- Definition 9.2: a Bregman potential on `C` yields the constrained-potential
strong-convexity statement for `ω + δ_C` on its effective domain, matching the textbook package
of standing assumptions via the canonical constrained-potential view. -/
theorem IsBregmanPotentialOn.strongConvexOn_add_indicator
    {ω : E → EReal} {C : Set E} {σ : ℝ} (hω : IsBregmanPotentialOn ω C σ) :
    StrongConvexOn (effective_domain (ω + δ_ C)) σ
      (fun x ↦ ((ω + δ_ C) x).toReal) := by
  -- Rewrite the constrained owner into the original feasible-set owner carried by `hω`.
  rw [StrongConvexOn, UniformConvexOn]
  refine ⟨?_, ?_⟩
  · -- The constrained effective domain is exactly the feasible set `C`.
    rw [effectiveDomainAddIndicator_eq hω]
    exact hω.strongConvexOn.1
  · intro x hx y hy a b ha hb hab
    have hxC : x ∈ C := by
      rwa [effectiveDomainAddIndicator_eq hω] at hx
    have hyC : y ∈ C := by
      rwa [effectiveDomainAddIndicator_eq hω] at hy
    have hzC : a • x + b • y ∈ C := hω.strongConvexOn.1 hxC hyC ha hb hab
    have hxValue : ((ω + δ_ C) x).toReal = (ω x).toReal := by
      simpa using toRealAddIndicator_eqOn (ω := ω) (C := C) hxC
    have hyValue : ((ω + δ_ C) y).toReal = (ω y).toReal := by
      simpa using toRealAddIndicator_eqOn (ω := ω) (C := C) hyC
    have hzValue : ((ω + δ_ C) (a • x + b • y)).toReal = (ω (a • x + b • y)).toReal := by
      simpa using toRealAddIndicator_eqOn (ω := ω) (C := C) hzC
    -- Transport the stored strong-convexity inequality through the feasible-point value bridge.
    rw [hzValue, hxValue, hyValue]
    exact hω.strongConvexOn.2 hxC hyC ha hb hab

end
