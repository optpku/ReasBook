/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Rademacher
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_12

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDual)
open Filter
open scoped Topology Gradient

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.13 is a `bridge/view` item in the chapter convex-analysis API. The source-facing
owners remain `effective_domain`, `finite_domain`, `is_convex_function`, and the extended-real
differentiability predicate `is_differentiable_at` from Definition 3.10, while the singleton
conclusion naturally lives on the continuous-dual bridge `strongDualSubdifferential`, because
`toDual` lands in `StrongDual ℝ E`. Here differentiability already supplies the interior
finite-domain hypothesis, and for a convex extended-real-valued function that interior finite point
forces the global no-`⊥` property needed by the directional-derivative owner theorem, so that
codomain restriction is derived API rather than primitive public data. -/
recall effective_domain
recall finite_domain
recall is_convex_function
recall is_differentiable_at
recall strongDualSubdifferential
recall subdifferential_nonempty_at_interior_point
recall properExtendedRealFunctionOfConvexInteriorFiniteDomain
recall directional_derivative_isGreatest_subgradient_pairings_at_interior_point
recall exists_subgradient_pairing_eq_directional_derivative_at_interior_point
recall directional_derivative_eq_of_mem_interior_of_hasFDerivAt
recall exists_closedBall_lipschitzOnWith_toReal_of_mem_interior
recall tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt

/-- Helper for Theorem 3.13: an interior finite-domain point of a convex function has a
nonempty strong-dual subdifferential. -/
  private lemma strongDualSubdifferential_nonempty_at_interiorFiniteDomain
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    Set.Nonempty (∂ₛf(x)) := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f x hconvex hx
  have hx_effective : x ∈ interior (effective_domain f) := by
    have h_ne_bot : ∀ y : E, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
    -- Interior finiteness becomes interior effective-domain membership once convexity
    -- rules out `⊥`.
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  rcases subdifferential_nonempty_at_interior_point f x hconvex hx_effective with ⟨g, hg⟩
  exact ⟨LinearMap.toContinuousLinearMap g, by simpa using hg⟩

/-- Helper for Theorem 3.13: every strong-dual subgradient at a differentiability point agrees
with the gradient dual. -/
private lemma eq_toDualGradient_of_memStrongDualSubdifferential_of_isDifferentiableAt
    (f : E → EReal) (x : E) (hconvex : is_convex_function f) (hdiff : is_differentiable_at f x)
    {g : StrongDual ℝ E} (hg : g ∈ ∂ₛf(x)) :
    g = toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f x hconvex hdiff.1
  have hx_effective : x ∈ interior (effective_domain f) := by
    have h_ne_bot : ∀ y : E, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
    -- The differentiability hypothesis already gives the interior finite-domain input.
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hdiff.1
  have hderiv :
      HasFDerivAt (fun y ↦ (f y).toReal)
        (toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)) x :=
    hdiff.2.hasGradientAt.hasFDerivAt
  ext d
  have hg_le :
      (g d : EReal) ≤ directional_derivative f x d := by
    have hgreatest :
        IsGreatest ((fun h : Module.Dual ℝ E ↦ (h d : EReal)) '' ∂f(x))
          (directional_derivative f x d) :=
      directional_derivative_isGreatest_subgradient_pairings_at_interior_point hconvex
        hx_effective
    exact hgreatest.2 ⟨g, hg, rfl⟩
  have hgrad :
      directional_derivative f x d =
        ((toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) d : ℝ) : EReal) := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
      directional_derivative_eq_of_mem_interior_of_hasFDerivAt hdiff.1 hderiv d
  have hleft :
      g d ≤ toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) d := by
    -- Compare the subgradient pairing to the directional derivative in direction `d`.
    rw [hgrad] at hg_le
    exact EReal.coe_le_coe_iff.mp hg_le
  have hneg_le :
      (g (-d) : EReal) ≤ directional_derivative f x (-d) := by
    have hgreatest :
        IsGreatest ((fun h : Module.Dual ℝ E ↦ (h (-d) : EReal)) '' ∂f(x))
          (directional_derivative f x (-d)) :=
      directional_derivative_isGreatest_subgradient_pairings_at_interior_point hconvex
        hx_effective
    exact hgreatest.2 ⟨g, hg, rfl⟩
  have hgrad_neg :
      directional_derivative f x (-d) =
        ((toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) (-d) : ℝ) : EReal) := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
      directional_derivative_eq_of_mem_interior_of_hasFDerivAt hdiff.1 hderiv (-d)
  have hright :
      toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) d ≤ g d := by
    -- Repeating the argument in direction `-d` yields the reverse inequality.
    rw [hgrad_neg] at hneg_le
    have hneg_real :
        -(g d) ≤ -(toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) d) := by
      simpa using (EReal.coe_le_coe_iff.mp hneg_le)
    linarith
  exact le_antisymm hleft hright

/-- Helper for Theorem 3.13: under uniqueness, one strong-dual subgradient realizes every
directional derivative by evaluation. -/
private lemma existsStrongDualSubgradient_withDirectionalDerivativeEq_apply_ofSubsingleton
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) (hunique : (∂ₛf(x)).Subsingleton) :
    ∃ g ∈ ∂ₛf(x), ∀ d : E, directional_derivative f x d = (g d : EReal) := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f x hconvex hx
  have hx_effective : x ∈ interior (effective_domain f) := by
    have h_ne_bot : ∀ y : E, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
    -- Convexity again removes the `⊥` branch from the finite-domain hypothesis.
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  rcases
      strongDualSubdifferential_nonempty_at_interiorFiniteDomain f x hconvex hx with
    ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  intro d
  have hpair :
      ∃ h ∈ ∂f(x), (h d : EReal) = directional_derivative f x d :=
    exists_subgradient_pairing_eq_directional_derivative_at_interior_point hconvex hx_effective
  rcases hpair with ⟨h, hh, hhd⟩
  have hh_strong : LinearMap.toContinuousLinearMap h ∈ ∂ₛf(x) := by
    simpa using hh
  have hh_eq : LinearMap.toContinuousLinearMap h = g := hunique hh_strong hg
  -- The directional derivative is attained by an owner subgradient, which must be the unique
  -- strong-dual witness after finite-dimensional transport.
  calc
    directional_derivative f x d = (h d : EReal) := hhd.symm
    _ = (g d : EReal) := by simpa using congrArg (fun k : StrongDual ℝ E ↦ (k d : EReal)) hh_eq

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.13: if the directional derivative is evaluation by `g`, then the
real-valued restriction has line derivative `g v` in direction `v`. -/
private lemma hasLineDerivAt_toReal_of_directionalDerivativeEq_apply
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) {g : StrongDual ℝ E}
    (hdir : ∀ d : E, directional_derivative f x d = (g d : EReal)) (v : E) :
    HasLineDerivAt ℝ (fun y ↦ (f y).toReal) (g v) x v := by
  have hdir_v : ∃ ℓv : ℝ, has_directional_derivative_at f x v ℓv :=
    exists_real_has_directional_derivative_at_of_convex_interior_point f x v hconvex hx
  rcases hdir_v with ⟨ℓv, hℓv_raw⟩
  have hℓv_eq : ℓv = g v := by
    exact_mod_cast
      (calc
      ((ℓv : ℝ) : EReal) = directional_derivative f x v := by
        symm
        exact directional_derivative_eq_of_has_directional_derivative_at hℓv_raw
      _ = (g v : EReal) := hdir v)
  have hℓv : has_directional_derivative_at f x v ((g v : ℝ) : EReal) := by
    simpa [hℓv_eq] using hℓv_raw
  have hright :
      Filter.Tendsto (fun t : ℝ ↦ ((f (x + t • v)).toReal - (f x).toReal) / t)
        (𝓝[>] (0 : ℝ)) (𝓝 (g v)) := by
    have hquotient :
        ∀ {d : E} {ℓ : ℝ},
          has_directional_derivative_at f x d (ℓ : EReal) →
            Tendsto (fun t : ℝ ↦ ((f (x + t • d)).toReal - (f x).toReal) / t)
              (𝓝[>] (0 : ℝ)) (𝓝 ℓ) :=
      tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt f x hx
    exact hquotient hℓv
  have hdir_neg : ∃ ℓneg : ℝ, has_directional_derivative_at f x (-v) ℓneg :=
    exists_real_has_directional_derivative_at_of_convex_interior_point f x (-v) hconvex hx
  rcases hdir_neg with ⟨ℓneg, hℓneg_raw⟩
  have hℓneg_eq : ℓneg = g (-v) := by
    exact_mod_cast
      (calc
      ((ℓneg : ℝ) : EReal) = directional_derivative f x (-v) := by
        symm
        exact directional_derivative_eq_of_has_directional_derivative_at hℓneg_raw
      _ = (g (-v) : EReal) := hdir (-v))
  have hℓneg : has_directional_derivative_at f x (-v) ((g (-v) : ℝ) : EReal) := by
    simpa [hℓneg_eq] using hℓneg_raw
  have hneg_right :
      Filter.Tendsto (fun t : ℝ ↦ ((f (x + t • (-v))).toReal - (f x).toReal) / t)
        (𝓝[>] (0 : ℝ)) (𝓝 (g (-v))) := by
    have hquotient :
        ∀ {d : E} {ℓ : ℝ},
          has_directional_derivative_at f x d (ℓ : EReal) →
            Tendsto (fun t : ℝ ↦ ((f (x + t • d)).toReal - (f x).toReal) / t)
              (𝓝[>] (0 : ℝ)) (𝓝 ℓ) :=
      tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt f x hx
    exact hquotient hℓneg
  have hleft_aux :
      Filter.Tendsto (fun t : ℝ ↦ ((f (x + (-t) • v)).toReal - (f x).toReal) / (-t))
        (𝓝[>] (0 : ℝ)) (𝓝 (g v)) := by
    -- The left quotient in direction `v` is the negative of the right quotient in direction `-v`.
    refine (show Tendsto (fun t : ℝ ↦ -(((f (x + t • (-v))).toReal - (f x).toReal) / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (g v)) from ?_).congr' ?_
    · simpa using hneg_right.neg
    · filter_upwards with t
      simp [div_eq_mul_inv, mul_comm]
  have hleft :
      Filter.Tendsto (fun t : ℝ ↦ ((f (x + t • v)).toReal - (f x).toReal) / t)
        (𝓝[<] (0 : ℝ)) (𝓝 (g v)) := by
    -- Transfer the positive-direction estimate for `-v` through `t ↦ -t`.
    refine (hleft_aux.comp
      (show Tendsto Neg.neg (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) by
        have hneg_tendsto :
            Tendsto Neg.neg (𝓝[<] (0 : ℝ)) (𝓝[>] (-(0 : ℝ))) :=
          tendsto_neg_nhdsLT
        simpa using hneg_tendsto)).congr' ?_
    filter_upwards with t
    simp
  have hderiv :
      HasDerivAt (fun t : ℝ ↦ (f (x + t • v)).toReal) (g v) (0 : ℝ) := by
    -- The left and right slope limits agree, so the one-dimensional derivative exists.
    let lineFun : ℝ → ℝ := fun t ↦ (f (x + t • v)).toReal
    have hleft_slope :
        Tendsto (slope lineFun 0) (𝓝[<] (0 : ℝ)) (𝓝 (g v)) := by
      rw [show slope lineFun 0 = fun t : ℝ ↦ (lineFun t - lineFun 0) / (t - 0) by
        funext t
        rw [slope_def_field]]
      simpa [lineFun] using hleft
    have hright_slope :
        Tendsto (slope lineFun 0) (𝓝[>] (0 : ℝ)) (𝓝 (g v)) := by
      rw [show slope lineFun 0 = fun t : ℝ ↦ (lineFun t - lineFun 0) / (t - 0) by
        funext t
        rw [slope_def_field]]
      simpa [lineFun] using hright
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    exact ⟨hleft_slope, hright_slope⟩
  simpa [HasLineDerivAt] using hderiv

/-- Helper for Theorem 3.13: linear directional derivatives plus local convex Lipschitz control
upgrade to a Fréchet derivative. -/
private lemma hasFDerivAt_toReal_of_directionalDerivativeEq_apply
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) {g : StrongDual ℝ E}
    (hdir : ∀ d : E, directional_derivative f x d = (g d : EReal)) :
    HasFDerivAt (fun y ↦ (f y).toReal) g x := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f x hconvex hx
  have hx_effective : x ∈ interior (effective_domain f) := by
    have h_ne_bot : ∀ y : E, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
    -- Local finiteness gives a genuine interior effective-domain neighborhood
    -- for the real-valued view.
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  obtain ⟨ε, hε_pos, L, hclosed_subset, hLip⟩ :=
    exists_closedBall_lipschitzOnWith_toReal_of_mem_interior f x hconvex
      (fun y _ ↦ IsProperExtendedRealFunction.ne_bot y) hx_effective
  obtain ⟨F, hF_lip, hF_eqOn⟩ := hLip.extend_real
  have hEqNhds : F =ᶠ[𝓝 x] fun y ↦ (f y).toReal := by
    -- The Lipschitz extension agrees with the original real-valued restriction on a neighborhood.
    filter_upwards [Metric.closedBall_mem_nhds x hε_pos] with y hy
    exact (hF_eqOn hy).symm
  have hF_line : ∀ v : E, HasLineDerivAt ℝ F (g v) x v := by
    intro v
    exact (hEqNhds.hasLineDerivAt_iff).2
      (hasLineDerivAt_toReal_of_directionalDerivativeEq_apply f x hconvex hx hdir v)
  have hFderiv : HasFDerivAt F g x := by
    -- Rademacher's finite-dimensional reconstruction turns the line
    -- derivatives into a Fréchet one.
    have hs_univ : Metric.sphere (0 : E) 1 ⊆ closure (Set.univ : Set E) := by simp
    exact hF_lip.hasFDerivAt_of_hasLineDerivAt_of_closure
      hs_univ
      fun v _ ↦ hF_line v
  exact (hEqNhds.hasFDerivAt_iff).1 hFderiv

-- Proof sketch: unpack `hdiff` as `x ∈ interior (finite_domain f)` plus differentiability of
-- `y ↦ (f y).toReal` at `x`. For a convex extended-real-valued function,
-- that interior finite point
-- rules out `⊥` globally, so the owner max formula for directional derivatives applies without a
-- primitive public `h_ne_bot` hypothesis. It identifies the directional derivative with the
-- pairing against the gradient. For any `g ∈ strongDualSubdifferential f x`,
-- the max formula bounds
-- `g d` by that directional derivative for every direction `d`, and applying this to both `d` and
-- `-d` forces `g` to coincide with the dual vector represented by
-- `∇ (fun y ↦ (f y).toReal) x`. Nonemptiness of the subdifferential at the
-- interior finite point
-- then gives the stated singleton equality.
/-- Forward implication for Theorem 3.13: if a convex extended-real-valued function is
differentiable at a point in the chapter sense `is_differentiable_at`, then its continuous-dual
subdifferential there is the singleton consisting of the dual vector represented by the
gradient. -/
theorem subdifferential_eq_singleton_gradient_of_differentiableAt
    (f : E → EReal) (x : E) (hconvex : is_convex_function f) (hdiff : is_differentiable_at f x) :
    ∂ₛf(x) = {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} := by
  -- Every subgradient equals the gradient dual, and interior-point existence supplies membership.
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · rcases
      strongDualSubdifferential_nonempty_at_interiorFiniteDomain f x hconvex hdiff.1 with
      ⟨g, hg⟩
    have hg_eq :
        g = toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) :=
      eq_toDualGradient_of_memStrongDualSubdifferential_of_isDifferentiableAt
        f x hconvex hdiff hg
    simpa [hg_eq] using hg
  · intro g hg
    exact
      eq_toDualGradient_of_memStrongDualSubdifferential_of_isDifferentiableAt
        f x hconvex hdiff hg

-- Proof sketch: the interior-point theorem `subdifferential_nonempty_at_interior_point` upgrades
-- the owner-set uniqueness hypothesis `Set.Subsingleton (strongDualSubdifferential f x)` to an
-- actual singleton description. Since `x ∈ interior (finite_domain f)`, it also lies in the
-- interior of `effective_domain f`, and convexity forces the ambient no-`⊥` property needed by
-- the directional-derivative owner theorem, so no stronger primitive hypothesis is needed
-- publicly. Let `g` be that unique subgradient. Translate the function by `x` and subtract the
-- affine functional defined by `g`; the resulting convex function still avoids `⊥` and has unique
-- subgradient `0` at the origin. The max formula then gives vanishing directional derivatives in
-- every direction, and the standard finite-dimensional convex argument upgrades this to
-- differentiability at the origin. Translating back yields differentiability of
-- `y ↦ (f y).toReal` at `x`, and the forward implication identifies the subdifferential with the
-- singleton of the gradient.
/-- Theorem 3.13 (2): if a convex extended-real-valued function has a unique continuous-dual
subgradient at an interior point of its finite domain, then the real-valued map
`y ↦ (f y).toReal` is differentiable there, equivalently `f` is differentiable there in the
chapter sense `is_differentiable_at`, and the subdifferential is the singleton of the
corresponding gradient. -/
theorem differentiableAt_and_subdifferential_eq_singleton_gradient_of_unique_subgradient
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f))
    (hunique : (∂ₛf(x)).Subsingleton) :
    is_differentiable_at f x ∧ ∂ₛf(x) = {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} := by
  rcases
      existsStrongDualSubgradient_withDirectionalDerivativeEq_apply_ofSubsingleton
        f x hconvex hx hunique with
    ⟨g, hg, hdir⟩
  have hderiv :
      HasFDerivAt (fun y ↦ (f y).toReal) g x :=
    hasFDerivAt_toReal_of_directionalDerivativeEq_apply f x hconvex hx hdir
  have hdiff : is_differentiable_at f x := by
    -- The directional-derivative normalization now upgrades to differentiability at `x`.
    exact ⟨hx, hderiv.differentiableAt⟩
  refine ⟨hdiff, ?_⟩
  -- The forward implication identifies the unique subgradient with the gradient dual.
  exact subdifferential_eq_singleton_gradient_of_differentiableAt f x hconvex hdiff

/-- Uniqueness criterion associated with Theorem 3.13: at an interior finite-domain point of a
convex extended-real-valued function, differentiability in the chapter sense is equivalent to the
continuous-dual subdifferential being a subsingleton. -/
theorem strongDualSubdifferential_subsingleton_iff_is_differentiable_at
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    (∂ₛf(x)).Subsingleton ↔ is_differentiable_at f x := by
  constructor
  · intro hsubsingleton
    exact
      (differentiableAt_and_subdifferential_eq_singleton_gradient_of_unique_subgradient
        f x hconvex hx hsubsingleton).1
  · intro hdiff
    rw [subdifferential_eq_singleton_gradient_of_differentiableAt f x hconvex hdiff]
    simp

/-- Singleton criterion associated with Theorem 3.13: at an interior finite-domain point of a
convex extended-real-valued function, differentiability in the chapter sense is equivalent to the
continuous-dual subdifferential being the singleton containing the gradient. -/
theorem subdifferential_eq_singleton_gradient_iff_is_differentiable_at
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    ∂ₛf(x) = {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} ↔
      is_differentiable_at f x := by
  constructor
  · intro hsub
    have hsubsingleton : (∂ₛf(x)).Subsingleton := by
      rw [hsub]
      simp
    exact
      (strongDualSubdifferential_subsingleton_iff_is_differentiable_at
        f x hconvex hx).1 hsubsingleton
  · intro hdiff
    exact subdifferential_eq_singleton_gradient_of_differentiableAt f x hconvex hdiff
