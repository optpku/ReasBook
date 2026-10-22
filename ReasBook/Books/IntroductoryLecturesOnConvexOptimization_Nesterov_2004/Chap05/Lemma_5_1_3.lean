/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm Topology ContDiff

noncomputable section

universe u

/- Lemma 5.1.3 lies in the chapter's self-concordance / line-derivative domain.

Sampled owner declarations in this domain:
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for the cubic
  directional derivative;
* `directionalSlice` from `Definition_5_0_10`, the chapter owner for affine-line restriction;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `associatedUnivariateFunction` from `Definition_5_0_12`, the source-facing reciprocal
  local-norm slice owner on the positivity domain;
* `associatedUnivariateFunctionDomain` from `Definition_5_0_12`, the source-facing owner for the
  natural positivity domain of that slice;
* nearby Chapter 5 line-derivative statements such as `Corollary_5_1_1` and `Theorem_5_1_4`,
  which already work over arbitrary complete real inner-product spaces.

Source/core/bridge triage:
* source-facing: the associated univariate reciprocal local-norm function and its natural domain
  along the affine line `t ↦ x + t • h`;
* core/canonical: `directionalSlice`, `thirdDirectionalDerivative f (x + t • h) h`, and
  `‖h‖[f; x + t • h]`;
* bridge/view: the ambient representative
  `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` of
  `associatedUnivariateFunction dom f x h` on `associatedUnivariateFunctionDomain dom f x h`.

Primitive data:
* the objective `f`;
* the line data `x` and `h`;
* the open domain carrying `C³` regularity;
* the single point `t` of `associatedUnivariateFunctionDomain dom f x h`.

Derived API:
* the source-facing derivative bound for the reciprocal local-norm slice in terms of the chapter
  owners `thirdDirectionalDerivative` and `hessianLocalNorm`;
* the explicit derivative formula for the canonical affine-line bridge
  `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` on
  `associatedUnivariateFunctionDomain dom f x h`.

This file therefore keeps `associatedUnivariateFunction` as the source-facing owner from
`Definition_5_0_12`, and its main public entry is the source-facing derivative bound for that
reciprocal local-norm slice. The explicit `HasDerivWithinAt` formula is only a bridge/view
statement because the one-variable calculus owner lives on ambient functions. Both statements use
the canonical ambient bridge `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` on the natural domain
`associatedUnivariateFunctionDomain dom f x h`, not an ad hoc zero-extension. The Chapter 5
differential-calculus API used here already lives over complete real inner-product spaces, so
finite dimensionality is not part of the canonical statement. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} {f : E → ℝ} {x h : E}

section AssociatedUnivariateFunctionBridge

local notation "sliceDomain" => associatedUnivariateFunctionDomain dom f x h
local notation "reciprocalLocalNormSlice" =>
  directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h

/-- Helper for Lemma 5.1.3: a `C²` real-valued function has a differentiable gradient because the
gradient is the Fréchet derivative transported through the Riesz isomorphism. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {y : E} (hf : ContDiffAt ℝ 2 f y) :
    DifferentiableAt ℝ (∇ f) y := by
  -- Rewrite the gradient through the continuous linear Riesz isomorphism and differentiate the
  -- Fréchet derivative field.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) y := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun z ↦ D (fderiv ℝ f z)) y
  exact (D.hasFDerivAt.comp y hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Lemma 5.1.3: the affine line restriction `directionalSlice f x h` is `C³` at a
parameter `t` whenever the shifted point `x + t • h` lies in the open `C³` domain `dom`. -/
private theorem directionalSlice_contDiffAt_three
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    {t : ℝ} (ht : x + t • h ∈ dom) :
    ContDiffAt ℝ 3 (directionalSlice f x h) t := by
  -- Restrict the ambient `C³` function to the affine line through `x` in direction `h`.
  have hft : ContDiffAt ℝ 3 f (x + t • h) := hcont.contDiffAt (hdom_open.mem_nhds ht)
  have hline : ContDiffAt ℝ 3 (fun s : ℝ ↦ x + s • h) t := by
    simpa using (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
      ContDiffAt ℝ 3 (fun s : ℝ ↦ x + s • h) t)
  simpa [directionalSlice] using hft.comp t hline

/-- Helper for Lemma 5.1.3: shifting the base point of the line slice rewrites the second
iterated derivative as the Hessian quadratic form at the shifted point. -/
private theorem directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    {s : ℝ} (hs : x + s • h ∈ dom) :
    iteratedDeriv 2 (directionalSlice f x h) s =
      inner ℝ h ((fderiv ℝ (∇ f) (x + s • h)) h) := by
  have hfAt : ContDiffAt ℝ 3 f (x + s • h) := hcont.contDiffAt (hdom_open.mem_nhds hs)
  have hfAtTwo : ContDiffAt ℝ 2 f (x + s • h) := hfAt.of_le (by norm_num)
  have hdiff : DifferentiableAt ℝ f (x + s • h) := hfAt.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ f) (x + s • h) := by
    exact differentiableAt_gradient_of_contDiffAt_two hfAtTwo
  have hshift :
      (fun z : ℝ ↦ directionalSlice f x h (s + z)) =
        directionalSlice f (x + s • h) h := by
    -- Translate the parameter so that the shifted slice is again a directional slice at `0`.
    funext z
    simp [directionalSlice, add_smul, add_assoc]
  calc
    iteratedDeriv 2 (directionalSlice f x h) s
      = iteratedDeriv 2 (fun z : ℝ ↦ directionalSlice f x h (s + z)) 0 := by
          simpa using congrArg (fun k : ℝ → ℝ ↦ k 0)
            (iteratedDeriv_comp_const_add 2 (directionalSlice f x h) s).symm
    _ = secondDirectionalDerivative f (x + s • h) h := by
          rw [hshift, secondDirectionalDerivative]
    _ = inner ℝ h (hessian f (x + s • h) h) := by
          exact secondDirectionalDerivative_eq_hessian_quadratic_form hfAtTwo
    _ = inner ℝ h ((fderiv ℝ (∇ f) (x + s • h)) h) := by
          simp [hessian]

/-- Helper for Lemma 5.1.3: shifting the base point of the line slice rewrites the third iterated
derivative as the chapter owner `thirdDirectionalDerivative` at the shifted point. -/
private theorem directionalSlice_iteratedDeriv_three_eq_thirdDirectionalDerivative
    (s : ℝ) :
    iteratedDeriv 3 (directionalSlice f x h) s =
      thirdDirectionalDerivative f (x + s • h) h := by
  have hshift :
      (fun z : ℝ ↦ directionalSlice f x h (s + z)) =
        directionalSlice f (x + s • h) h := by
    -- The same translation identity works at third order.
    funext z
    simp [directionalSlice, add_smul, add_assoc]
  calc
    iteratedDeriv 3 (directionalSlice f x h) s
      = iteratedDeriv 3 (fun z : ℝ ↦ directionalSlice f x h (s + z)) 0 := by
          simpa using congrArg (fun k : ℝ → ℝ ↦ k 0)
            (iteratedDeriv_comp_const_add 3 (directionalSlice f x h) s).symm
    _ = thirdDirectionalDerivative f (x + s • h) h := by
          rw [hshift, thirdDirectionalDerivative]

/-- Helper for Lemma 5.1.3: the natural slice domain is a neighborhood of every one of its
points, because both the ambient domain condition and the local-norm positivity condition are
open along the affine line. -/
private theorem associatedUnivariateFunctionDomain_mem_nhds
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    {t : ℝ} (ht : t ∈ sliceDomain) :
    sliceDomain ∈ 𝓝 t := by
  rcases (mem_associatedUnivariateFunctionDomain_iff dom f x h t).1 ht with ⟨ht_dom, ht_pos⟩
  let q : ℝ → ℝ := fun s ↦ iteratedDeriv 2 (directionalSlice f x h) s
  have hslice3 : ContDiffAt ℝ 3 (directionalSlice f x h) t :=
    directionalSlice_contDiffAt_three hdom_open hcont ht_dom
  have hq_diff : DifferentiableAt ℝ q t := by
    -- A `C³` slice has a differentiable second iterated derivative.
    have hdiffWithin :
        DifferentiableWithinAt ℝ
          (iteratedDerivWithin 2 (directionalSlice f x h) Set.univ)
          Set.univ
          t := by
      exact
        hslice3.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin
          (by norm_num : (2 : ℕ∞ω) < (3 : ℕ∞ω))
          (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)))
    simpa [q, iteratedDerivWithin_univ, differentiableWithinAt_univ] using hdiffWithin
  have hq_pos : 0 < q t := by
    -- Positivity of the local norm is exactly positivity of the shifted slice Hessian quadratic
    -- form.
    have hsqrt_pos : 0 < Real.sqrt (q t) := by
      simpa [q, hessianLocalNorm_def,
        directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form hdom_open hcont ht_dom] using
        ht_pos
    exact Real.sqrt_pos.mp hsqrt_pos
  have hline_mem : {s : ℝ | x + s • h ∈ dom} ∈ 𝓝 t := by
    -- Openness of `dom` pulls back to a neighborhood along the affine line.
    have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • h) t := by
      simpa using
        (continuousAt_const.add (continuousAt_id.smul continuousAt_const) :
          ContinuousAt (fun s : ℝ ↦ x + s • h) t)
    exact hline_cont.preimage_mem_nhds (hdom_open.mem_nhds ht_dom)
  have hq_mem : {s : ℝ | 0 < q s} ∈ 𝓝 t := by
    -- Continuity of the second slice derivative preserves its positivity near `t`.
    exact hq_diff.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hq_pos)
  refine Filter.mem_of_superset (Filter.inter_mem hline_mem hq_mem) ?_
  intro s hs
  rcases hs with ⟨hs_dom, hs_q⟩
  refine (mem_associatedUnivariateFunctionDomain_iff dom f x h s).2 ?_
  refine ⟨hs_dom, ?_⟩
  -- Convert the positivity of the quadratic form back to positivity of the local norm.
  have hsqrt_pos : 0 < Real.sqrt (q s) := Real.sqrt_pos.mpr hs_q
  simpa [q, hessianLocalNorm_def,
    directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form hdom_open hcont hs_dom] using
    hsqrt_pos

/-- Helper for Lemma 5.1.3: the canonical ambient reciprocal local-norm slice has the displayed
within-derivative formula on its natural positivity domain. -/
private theorem reciprocalLocalNormSlice_hasDerivWithinAt
    {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain) :
    HasDerivWithinAt
      reciprocalLocalNormSlice
      (-(thirdDirectionalDerivative f (x + t • h) h /
          (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ))))
      sliceDomain
      t := by
  rcases (mem_associatedUnivariateFunctionDomain_iff dom f x h t).1 ht with ⟨ht_dom, ht_pos⟩
  let q : ℝ → ℝ := fun s ↦ iteratedDeriv 2 (directionalSlice f x h) s
  have hslice3 : ContDiffAt ℝ 3 (directionalSlice f x h) t :=
    directionalSlice_contDiffAt_three hdom_open hcont ht_dom
  have hq_diff : DifferentiableAt ℝ q t := by
    -- A `C³` slice has a differentiable second iterated derivative at the chosen parameter.
    have hdiffWithin :
        DifferentiableWithinAt ℝ
          (iteratedDerivWithin 2 (directionalSlice f x h) Set.univ)
          Set.univ
          t := by
      exact
        hslice3.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin
          (by norm_num : (2 : ℕ∞ω) < (3 : ℕ∞ω))
          (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)))
    simpa [q, iteratedDerivWithin_univ, differentiableWithinAt_univ] using hdiffWithin
  have hq_hasDerivAt :
      HasDerivAt q (thirdDirectionalDerivative f (x + t • h) h) t := by
    -- The derivative of the second iterated derivative is the third iterated derivative.
    have hderiv_q :
        deriv q t = thirdDirectionalDerivative f (x + t • h) h := by
      simpa [q, iteratedDeriv_succ] using
        directionalSlice_iteratedDeriv_three_eq_thirdDirectionalDerivative (f := f) (x := x)
          (h := h) t
    exact hq_diff.hasDerivAt.congr_deriv hderiv_q
  have hq_pos : 0 < q t := by
    have hsqrt_pos : 0 < Real.sqrt (q t) := by
      simpa [q, hessianLocalNorm_def,
        directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form hdom_open hcont ht_dom] using
        ht_pos
    exact Real.sqrt_pos.mp hsqrt_pos
  have hq_ne : q t ≠ 0 := ne_of_gt hq_pos
  have hsqrt_ne : Real.sqrt (q t) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hq_pos)
  have hq_within :
      HasDerivWithinAt q (thirdDirectionalDerivative f (x + t • h) h) sliceDomain t :=
    hq_hasDerivAt.hasDerivWithinAt
  have hsqrt_within :
      HasDerivWithinAt
        (fun s : ℝ ↦ Real.sqrt (q s))
        (thirdDirectionalDerivative f (x + t • h) h / (2 * Real.sqrt (q t)))
        sliceDomain
        t := by
    -- Differentiate the square root of the Hessian quadratic form along the slice.
    exact hq_within.sqrt hq_ne
  have hinv_within :
      HasDerivWithinAt
        (fun s : ℝ ↦ (Real.sqrt (q s))⁻¹)
        (-(thirdDirectionalDerivative f (x + t • h) h / (2 * Real.sqrt (q t))) /
          (Real.sqrt (q t)) ^ (2 : ℕ))
        sliceDomain
        t := by
    -- Then differentiate the reciprocal to obtain the reciprocal local norm derivative.
    exact hsqrt_within.inv hsqrt_ne
  have hfun :
      reciprocalLocalNormSlice =ᶠ[𝓝[sliceDomain] t]
        fun s : ℝ ↦ (Real.sqrt (q s))⁻¹ := by
    -- On the slice domain, the ambient representative is exactly the reciprocal square root of
    -- the shifted Hessian quadratic form.
    filter_upwards [self_mem_nhdsWithin] with s hs
    rcases (mem_associatedUnivariateFunctionDomain_iff dom f x h s).1 hs with ⟨hs_dom, _⟩
    simp [q, directionalSlice, one_div, hessianLocalNorm_def,
      directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form hdom_open hcont hs_dom]
  have hrewritten :
      HasDerivWithinAt
        reciprocalLocalNormSlice
        (-(thirdDirectionalDerivative f (x + t • h) h / (2 * Real.sqrt (q t))) /
          (Real.sqrt (q t)) ^ (2 : ℕ))
        sliceDomain
        t := by
    exact hinv_within.congr_of_eventuallyEq_of_mem hfun ht
  have hnorm_ne : ‖h‖[f; x + t • h] ≠ 0 := ne_of_gt ht_pos
  -- Rewrite the derivative coefficient from the auxiliary `q` notation back to the chapter
  -- owners `thirdDirectionalDerivative` and `hessianLocalNorm`.
  have hcoeff :
      (-(thirdDirectionalDerivative f (x + t • h) h / (2 * Real.sqrt (q t))) /
          (Real.sqrt (q t)) ^ (2 : ℕ)) =
        (-(thirdDirectionalDerivative f (x + t • h) h /
            (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ)))) := by
    have hsqrt_eq : Real.sqrt (q t) = ‖h‖[f; x + t • h] := by
      calc
        Real.sqrt (q t)
          = Real.sqrt (inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h)) := by
              congr 1
              exact
                directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form
                  (f := f) (x := x) (h := h) hdom_open hcont ht_dom
        _ = ‖h‖[f; x + t • h] := by
              simpa [hessianLocalNorm_def, hessian]
    rw [hsqrt_eq]
    field_simp [hnorm_ne]
  exact hrewritten.congr_deriv hcoeff

-- Proof sketch: differentiate the reciprocal local-norm slice on its natural domain using the
-- explicit `HasDerivWithinAt` bridge below; the uniform quotient hypothesis bounds the resulting
-- derivative formula by `M_f` at the chosen point.
/-- Lemma 5.1.3: if `f` is `C³` on an open set `dom` and the quotient
`|D³f(x + t h)[h,h,h]| / (2 ‖h‖[f; x + t • h]^3)` is bounded by `M_f` throughout the natural
domain of the associated univariate function, then the derivative within that domain of the
canonical ambient representative `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h`, equivalently
`associatedUnivariateFunction dom f x h`, has absolute value at most `M_f` at every
`t ∈ associatedUnivariateFunctionDomain dom f x h`. -/
theorem abs_derivWithin_associatedUnivariateFunction_le
    {Mf : NNReal} {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain)
    (hbound :
      ∀ {s : ℝ}, s ∈ sliceDomain →
        |thirdDirectionalDerivative f (x + s • h) h| /
            (2 * ‖h‖[f; x + s • h] ^ (3 : ℕ)) ≤ (Mf : ℝ)) :
    |derivWithin
        reciprocalLocalNormSlice
        sliceDomain
        t| ≤ (Mf : ℝ) := by
  -- Differentiate the reciprocal local-norm slice using the explicit bridge formula.
  have hderiv :
      HasDerivWithinAt
        reciprocalLocalNormSlice
        (-(thirdDirectionalDerivative f (x + t • h) h /
            (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ))))
        sliceDomain
        t :=
    reciprocalLocalNormSlice_hasDerivWithinAt hdom_open hcont ht
  have hunique : UniqueDiffWithinAt ℝ sliceDomain t := by
    -- The natural slice domain is a neighborhood of `t`, so it has unique derivatives there.
    exact uniqueDiffWithinAt_of_mem_nhds
      (associatedUnivariateFunctionDomain_mem_nhds hdom_open hcont ht)
  rw [hderiv.derivWithin hunique]
  -- The hypothesis `hbound` is exactly the absolute-value estimate for the explicit derivative.
  have ht_pos : 0 < ‖h‖[f; x + t • h] :=
    (mem_associatedUnivariateFunctionDomain_iff dom f x h t).1 ht |>.2
  have htwo_abs : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  have hnorm_abs : |‖h‖[f; x + t • h]| = ‖h‖[f; x + t • h] := abs_of_pos ht_pos
  simpa [abs_neg, abs_div, abs_mul, htwo_abs, hnorm_abs] using hbound ht

-- Proof sketch: let `g(t) = hessianLocalNorm f (x + t • h) h ^ 2`, so `g` is the Hessian
-- quadratic form along the line. Differentiate `g` using the `C³` regularity of `f` on the open
-- set containing the line, identify `g'` with `thirdDirectionalDerivative f (x + t • h) h`, and
-- then apply the chain rule to `g ↦ g^(-1/2)` rewritten as the reciprocal local norm.
/-- Bridge form of Lemma 5.1.3: at each `t ∈ associatedUnivariateFunctionDomain dom f x h` the
canonical ambient representative `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h`, equivalently
`associatedUnivariateFunction dom f x h` on its natural domain, has derivative within that domain
`-D³f(x + t h)[h,h,h] / (2 ‖h‖[f; x + t • h]^3)`. -/
theorem associatedUnivariateFunction_hasDerivWithinAt
    {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain) :
    HasDerivWithinAt
      reciprocalLocalNormSlice
      (-(thirdDirectionalDerivative f (x + t • h) h /
          (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ))))
      sliceDomain
      t := by
  -- Reuse the file-local bridge theorem proved before the bound corollary.
  simpa using reciprocalLocalNormSlice_hasDerivWithinAt hdom_open hcont ht

end AssociatedUnivariateFunctionBridge

end
