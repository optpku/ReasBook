/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30

open InnerProductSpace (toDual)
open Filter
open scoped Pointwise Topology Gradient

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Theorem 3.35 is `source-facing` for composite first-order optimality. Its primitive convex-analysis
notions are already owned upstream by `effective_domain` and `is_convex_function`, while the
source-facing stationarity condition itself is already owned in Definition 3.17 by
`is_stationary_point`. The continuous-dual set `strongDualSubdifferential` is only the
`bridge/view` used inside that owner predicate, so this file states its conclusions in terms of
`is_stationary_point` instead of duplicating the defining condition. For this item, the primitive
source data is the properness of `f`, the properness and convexity of `g`, the qualification
`effective_domain g ⊆ interior (finite_domain f)`, the feasibility point
`xStar ∈ effective_domain g`, the chapter differentiability owner `is_differentiable_at f xStar`,
and the corresponding local or global optimality statement for the composite problem
`fun x ↦ f x + g x`.
-/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall is_stationary_point

-- Semantic recall: `lean_leansearch` surfaced only generic `IsLocalMin` calculus lemmas, so this
-- item stays on the project owners `IsProperExtendedRealFunction` and `is_stationary_point`.

section CompositeContext

variable {f g : E → EReal}

local notation "F" => fun x ↦ f x + g x

variable {xStar : E}

/-- Helper for Theorem 3.35: local minimality of `f + g` along the segment from `xStar` to `y`
forces the gradient of `f` at `xStar` to dominate the loss in `g`. -/
lemma compositeDirectionalLowerBound_of_isLocalMin
    (hgproper : IsProperExtendedRealFunction g)
    (hgconvex : is_convex_function g)
    (hdom : effective_domain g ⊆ interior (finite_domain f))
    (hxStar : xStar ∈ effective_domain g)
    (hdiff : is_differentiable_at f xStar)
    (hlocal : IsLocalMin F xStar)
    {y : E} (hy : y ∈ effective_domain g) :
    (g xStar).toReal - (g y).toReal ≤
      toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) (y - xStar) := by
  letI : IsProperExtendedRealFunction g := hgproper
  let line : ℝ → E := fun t ↦ (1 - t) • xStar + t • y
  have hxStar_finite : xStar ∈ finite_domain f := interior_subset (hdom hxStar)
  have hlineLocal : IsLocalMin (fun t : ℝ ↦ F (line t)) 0 := by
    -- Compose the local minimum with the affine line segment through `xStar` and `y`.
    have hlocalAtLineZero : IsLocalMin F (line 0) := by
      simpa [line] using hlocal
    exact hlocalAtLineZero.comp_continuous (by
      fun_prop)
  have hlineRight :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), F xStar ≤ F (line t) := by
    -- Restrict the local comparison inequality to the right-hand neighborhood used by the
    -- directional derivative.
    simpa [IsMinFilter, line] using hlineLocal.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi (0 : ℝ))
  have hlt1 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 := by
    simpa [Set.mem_Iio] using
      (show Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hquotTendsto :
      Tendsto (fun t : ℝ ↦ ((f (line t)).toReal - (f xStar).toReal) / t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) (y - xStar))) := by
    have hlineDeriv :
        HasLineDerivAt ℝ (fun z ↦ (f z).toReal)
          (toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) (y - xStar))
          xStar (y - xStar) := by
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
        hdiff.2.hasGradientAt.hasFDerivAt.hasLineDerivAt (y - xStar)
    -- Rewrite the line derivative through the segment parametrization.
    simpa [line, sub_eq_add_neg, add_smul, smul_sub, add_comm, add_left_comm, add_assoc,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hlineDeriv.tendsto_slope_zero_right
  have hlowerEventually :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (g xStar).toReal - (g y).toReal ≤
          ((f (line t)).toReal - (f xStar).toReal) / t := by
    filter_upwards [hlineRight, hpos, hlt1] with t hmin htpos ht1
    have hline_mem_g : line t ∈ effective_domain g := by
      -- Convexity keeps the segment between `xStar` and `y` inside `effective_domain g`.
      have hseg :
          t • y + (1 - t) • xStar ∈ effective_domain g :=
        combo_mem_effective_domain_of_is_convex_function hgconvex hy hxStar ⟨htpos.le, ht1.le⟩
      simpa [line, add_comm, add_left_comm, add_assoc] using hseg
    have hline_finite : line t ∈ finite_domain f := interior_subset (hdom hline_mem_g)
    have hFxStar :
        F xStar = (((f xStar).toReal + (g xStar).toReal : ℝ) : EReal) := by
      -- At `xStar`, both terms are finite, so the composite objective is the corresponding
      -- real sum.
      have hFtop : F xStar ≠ ⊤ := by
        change f xStar + g xStar ≠ ⊤
        exact (EReal.add_lt_top (mem_effective_domain.mp hxStar_finite.1).ne
          (mem_effective_domain.mp hxStar).ne).ne
      have hFbot : F xStar ≠ ⊥ := by
        change f xStar + g xStar ≠ ⊥
        simpa using
          (EReal.add_ne_bot_iff : f xStar + g xStar ≠ ⊥ ↔ f xStar ≠ ⊥ ∧ g xStar ≠ ⊥).2
            ⟨hxStar_finite.2, hgproper.ne_bot xStar⟩
      calc
        F xStar = (((F xStar).toReal : ℝ) : EReal) := by
          symm
          exact EReal.coe_toReal hFtop hFbot
        _ = (((f xStar).toReal + (g xStar).toReal : ℝ) : EReal) := by
          congr 1
          change (f xStar + g xStar).toReal = _
          exact EReal.toReal_add (mem_effective_domain.mp hxStar_finite.1).ne hxStar_finite.2
            (mem_effective_domain.mp hxStar).ne (hgproper.ne_bot xStar)
    have hFline :
        F (line t) = (((f (line t)).toReal + (g (line t)).toReal : ℝ) : EReal) := by
      -- The same finiteness rewrite holds at nearby feasible comparison points on the segment.
      have hFtop : F (line t) ≠ ⊤ := by
        change f (line t) + g (line t) ≠ ⊤
        exact (EReal.add_lt_top (mem_effective_domain.mp hline_finite.1).ne
          (mem_effective_domain.mp hline_mem_g).ne).ne
      have hFbot : F (line t) ≠ ⊥ := by
        change f (line t) + g (line t) ≠ ⊥
        simpa using
          (EReal.add_ne_bot_iff : f (line t) + g (line t) ≠ ⊥ ↔
              f (line t) ≠ ⊥ ∧ g (line t) ≠ ⊥).2
            ⟨hline_finite.2, hgproper.ne_bot (line t)⟩
      calc
        F (line t) = (((F (line t)).toReal : ℝ) : EReal) := by
          symm
          exact EReal.coe_toReal hFtop hFbot
        _ = (((f (line t)).toReal + (g (line t)).toReal : ℝ) : EReal) := by
          congr 1
          change (f (line t) + g (line t)).toReal = _
          exact EReal.toReal_add (mem_effective_domain.mp hline_finite.1).ne hline_finite.2
            (mem_effective_domain.mp hline_mem_g).ne (hgproper.ne_bot (line t))
    have hminReal :
        (f xStar).toReal + (g xStar).toReal ≤
          (f (line t)).toReal + (g (line t)).toReal := by
      have hminCoe :
          (((f xStar).toReal + (g xStar).toReal : ℝ) : EReal) ≤
            (((f (line t)).toReal + (g (line t)).toReal : ℝ) : EReal) := by
        simpa [hFxStar, hFline] using hmin
      exact EReal.coe_le_coe_iff.mp hminCoe
    have hglineLe :
        (g (line t)).toReal ≤
          (1 - t) * (g xStar).toReal + t * (g y).toReal := by
      have hsum : (1 - t) + t = 1 := by ring
      have hconvReal :
          ConvexOn ℝ (effective_domain g) (fun z ↦ (g z).toReal) :=
        convexOn_toReal_of_is_convex_function_of_proper g hgconvex
      -- Apply the real-valued convexity inequality for `g` on the segment.
      simpa [line, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
        hconvReal.2 hxStar hy (sub_nonneg.mpr ht1.le) htpos.le hsum
    have hmul :
        t * ((g xStar).toReal - (g y).toReal) ≤
          (f (line t)).toReal - (f xStar).toReal := by
      -- Combine local minimality of `f + g` with convexity of `g` and rearrange.
      linarith
    have hmul' :
        ((g xStar).toReal - (g y).toReal) * t ≤
          (f (line t)).toReal - (f xStar).toReal := by
      simpa [mul_comm] using hmul
    exact (le_div_iff₀ htpos).2 hmul'
  -- Pass to the right-hand limit to recover the gradient bound.
  exact ge_of_tendsto hquotTendsto hlowerEventually

/-- Helper for Theorem 3.35: convex differentiability identifies the gradient dual with an owner
subgradient of `f`. -/
lemma toDualGradient_mem_subdifferential_of_convex_differentiableAt
    (hfconvex : is_convex_function f)
    (hdiff : is_differentiable_at f xStar) :
    (toDual ℝ E (∇ (fun y ↦ (f y).toReal) xStar) : Module.Dual ℝ E) ∈
      subdifferential f xStar := by
  have hstrong :
      toDual ℝ E (∇ (fun y ↦ (f y).toReal) xStar) ∈ ∂ₛf(xStar) := by
    rw [subdifferential_eq_singleton_gradient_of_differentiableAt f xStar hfconvex hdiff]
    simp
  simpa [mem_strongDualSubdifferential] using hstrong

/-- Helper for Theorem 3.35: stationarity of the composite problem yields a zero owner
subgradient for `f + g`. -/
lemma zero_mem_subdifferential_composite_of_isStationaryPoint
    (hfconvex : is_convex_function f)
    (hstat : is_stationary_point f g xStar) :
    (0 : Module.Dual ℝ E) ∈ subdifferential F xStar := by
  rw [is_stationary_point_iff] at hstat
  have hsubf :
      (toDual ℝ E (∇ (fun y ↦ (f y).toReal) xStar) : Module.Dual ℝ E) ∈
        subdifferential f xStar :=
    toDualGradient_mem_subdifferential_of_convex_differentiableAt
      (f := f) (xStar := xStar) hfconvex hstat.1
  have hsubg :
      (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) xStar) : Module.Dual ℝ E) ∈
        subdifferential g xStar :=
    hstat.2
  have hsum :
      (0 : Module.Dual ℝ E) ∈ subdifferential f xStar + subdifferential g xStar := by
    -- The gradient subgradient for `f` and the stationary subgradient for `g` cancel exactly.
    rw [Set.mem_add]
    refine ⟨(toDual ℝ E (∇ (fun y ↦ (f y).toReal) xStar) : Module.Dual ℝ E), hsubf,
      (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) xStar) : Module.Dual ℝ E), hsubg, ?_⟩
    simp
  change (0 : Module.Dual ℝ E) ∈ subdifferential (fun x ↦ f x + g x) xStar
  exact sum_subdifferential_subset_subdifferential_add f g xStar hsum

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.35: outside `effective_domain g`, the composite objective `f + g`
collapses to `⊤`. -/
lemma compositeObjective_eq_top_of_not_memEffectiveDomain
    (hfproper : IsProperExtendedRealFunction f)
    {y : E} (hy : y ∉ effective_domain g) :
    F y = ⊤ := by
  have hgy : g y = ⊤ := le_antisymm le_top (le_of_not_gt hy)
  -- Once `g y = ⊤`, properness of `f` rules out the exceptional `⊥ + ⊤` case.
  change f y + g y = ⊤
  rw [hgy]
  simpa using EReal.add_top_of_ne_bot (hfproper.ne_bot y)

-- Proof sketch: use local minimality of the composite objective on `E` together with the
-- qualification `effective_domain g ⊆ interior (finite_domain f)` to restrict to nearby feasible
-- comparison points. Convexity of `g` turns the local minimality inequality into a one-sided
-- directional inequality for `f` at `xStar`, and differentiability identifies that directional
-- derivative with evaluation against the gradient.
/-- Necessary-direction theorem for Theorem 3.35: under the composite-problem setup where `f` and
`g` are proper, `g` is
convex, and `effective_domain g ⊆ interior (finite_domain f)`, if
`xStar ∈ effective_domain g` is a local minimizer of the global problem `x ↦ f x + g x` and `f`
is differentiable at `xStar`, then `xStar` is stationary for the composite problem. Unfolding
`is_stationary_point f g xStar` recovers the textbook condition `-∇ f(xStar) ∈ ∂ g(xStar)`. -/
theorem is_stationary_point_of_isLocalMin
    (hfproper : IsProperExtendedRealFunction f)
    (hgproper : IsProperExtendedRealFunction g)
    (hgconvex : is_convex_function g)
    (hdom : effective_domain g ⊆ interior (finite_domain f))
    (hxStar : xStar ∈ effective_domain g)
    (hdiff : is_differentiable_at f xStar)
    (hlocal : IsLocalMin F xStar) :
    is_stationary_point f g xStar := by
  let _ := hfproper
  rw [is_stationary_point_iff]
  refine ⟨hdiff, ?_⟩
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hxStar, ?_⟩
  intro y hy
  have hgrad :
      (g xStar).toReal - (g y).toReal ≤
        toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) (y - xStar) :=
    compositeDirectionalLowerBound_of_isLocalMin
      (f := f) (g := g) (xStar := xStar)
      hgproper hgconvex hdom hxStar hdiff hlocal hy
  have hgx :
      g xStar = (((g xStar).toReal : ℝ) : EReal) := by
    symm
    exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar)) (hgproper.ne_bot xStar)
  have hgy :
      g y = (((g y).toReal : ℝ) : EReal) := by
    symm
    exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hy)) (hgproper.ne_bot y)
  have hreal' :
      (g xStar).toReal -
          toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) (y - xStar) ≤
        (g y).toReal := by
    linarith
  have hreal :
      (g xStar).toReal +
          ((-toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) : Module.Dual ℝ E) (y - xStar)) ≤
        (g y).toReal := by
    -- Rewrite the negative functional evaluation into subtraction once, then reuse the real bound.
    simpa [LinearMap.neg_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hreal'
  have hEReal :
      (((g xStar).toReal +
          ((-toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) : Module.Dual ℝ E) (y - xStar)) : ℝ) :
          EReal) ≤ (((g y).toReal : ℝ) : EReal) :=
    EReal.coe_le_coe hreal
  have htarget :
      g xStar +
          (((-toDual ℝ E (∇ (fun z ↦ (f z).toReal) xStar) : Module.Dual ℝ E) (y - xStar) : ℝ) :
            EReal) ≤
        g y := by
    rw [hgx, hgy]
    simpa [EReal.coe_add] using hEReal
  simpa [ge_iff_le] using htarget

-- Proof sketch: for the forward implication, apply part (1) to a global minimizer of the problem
-- on `E`. For the converse implication, combine the subgradient inequality for `g` with the
-- first-order convexity inequality for differentiable convex `f`, then add the two inequalities
-- to obtain global minimality of `f + g` on `Set.univ`.
/-- Helper for Theorem 3.35: under the same composite-problem setup, if `f` is also convex and
differentiable at `xStar ∈ effective_domain g`, then `xStar` is a global minimizer of the problem
`x ↦ f x + g x` on `E` if and only if it is stationary. Unfolding
`is_stationary_point f g xStar` recovers the textbook condition `-∇ f(xStar) ∈ ∂ g(xStar)`. -/
theorem isMinOn_univ_iff_is_stationary_point
    (hfproper : IsProperExtendedRealFunction f)
    (hgproper : IsProperExtendedRealFunction g)
    (hgconvex : is_convex_function g)
    (hdom : effective_domain g ⊆ interior (finite_domain f))
    (hxStar : xStar ∈ effective_domain g)
    (hdiff : is_differentiable_at f xStar)
    (hfconvex : is_convex_function f) :
    IsMinOn F Set.univ xStar ↔
      is_stationary_point f g xStar := by
  constructor
  · intro hmin
    have hlocal : IsLocalMin F xStar := hmin.isLocalMin (by simp)
    -- A global minimizer is in particular a local minimizer, so part (1) applies directly.
    exact is_stationary_point_of_isLocalMin
      hfproper hgproper hgconvex hdom hxStar hdiff hlocal
  · intro hstat
    have hFdom : (effective_domain F).Nonempty := by
      have hxStar_finite : xStar ∈ finite_domain f := interior_subset (hdom hxStar)
      refine ⟨xStar, ?_⟩
      -- The feasible point `xStar` is finite for both summands, so the composite is finite there.
      change f xStar + g xStar < ⊤
      simpa using
        EReal.add_lt_top (mem_effective_domain.mp hxStar_finite.1).ne
          (mem_effective_domain.mp hxStar).ne
    -- Stationarity gives a zero subgradient for the composite, and Fermat's theorem closes the
    -- global minimality claim.
    exact
      (isMinOn_univ_iff_zero_mem_subdifferential (f := F) hFdom).2
        (zero_mem_subdifferential_composite_of_isStationaryPoint
          (f := f) (g := g) (xStar := xStar) hfconvex hstat)

/-- Theorem 3.35: under the composite-problem setup, stationarity is equivalent to minimizing the
composite objective on `effective_domain g`. -/
theorem isMinOn_iff_is_stationary_point
    (hfproper : IsProperExtendedRealFunction f)
    (hgproper : IsProperExtendedRealFunction g)
    (hgconvex : is_convex_function g)
    (hdom : effective_domain g ⊆ interior (finite_domain f))
    (hxStar : xStar ∈ effective_domain g)
    (hdiff : is_differentiable_at f xStar)
    (hfconvex : is_convex_function f) :
    IsMinOn F (effective_domain g) xStar ↔
      is_stationary_point f g xStar := by
  constructor
  · intro hmin
    have huniv : IsMinOn F Set.univ xStar := by
      rw [isMinOn_univ_iff]
      intro y
      by_cases hy : y ∈ effective_domain g
      · exact (isMinOn_iff.mp hmin) y hy
      · calc
          F xStar ≤ ⊤ := le_top
          _ = F y := by
            symm
            exact compositeObjective_eq_top_of_not_memEffectiveDomain
              (f := f) (g := g) hfproper hy
    exact
      (isMinOn_univ_iff_is_stationary_point
        hfproper hgproper hgconvex hdom hxStar hdiff hfconvex).1 huniv
  · intro hstat
    have huniv :=
      (isMinOn_univ_iff_is_stationary_point
        hfproper hgproper hgconvex hdom hxStar hdiff hfconvex).2 hstat
    rw [isMinOn_iff] at huniv ⊢
    -- Restrict the global minimality inequality to the feasible set `effective_domain g`.
    intro y hy
    exact huniv y (by simp)

end CompositeContext

end
