/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm Topology ContDiff

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

/- Proposition 5.0.15 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith` in `Definition_5_1_1`, the quantitative source-facing owner for
  self-concordance on a domain;
* `hessian` in `Chap01/Definition_1_4_16`, the canonical second-order operator owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` in `Definition_5_1_1`, the chapter owner for
  the local Hessian norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the
  source-facing owner for the Dikin-radius hypothesis.

Source/core/bridge triage:
* source-facing: the pointwise Hessian comparison between `x` and `y` under the textbook
  open-Dikin hypothesis;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `hessian f z`, and `W⁰[f; x](r)`;
* bridge/view: the local-norm inequality encoded by membership in `W⁰[f; x](r)`.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, and a function `f`;
* points `x y : E` and a radius `r`;
* the owner hypothesis `hself : IsSelfConcordantOnWith dom Mf f`;
* the source-facing inputs `hx : x ∈ dom`, `hy : y ∈ dom`, `hr : r < 1 / (Mf : ℝ)`, and
  `hxy : y ∈ W⁰[f; x](r)`, where `(hy, hxy)` together encode the textbook membership
  `y ∈ W(x; r) = {z ∈ dom f : ‖z - x‖_x < r}`.

Derived API:
* the lower and upper Loewner-order bounds comparing `hessian f x` and `hessian f y`.

The theorem should therefore stay directly on the bundled self-concordance owner and the canonical
Hessian owner, while exposing the exact-local-radius comparison as the reusable owner-level API and
carrying the domain-membership half of the textbook Dikin condition explicitly because the raw
owner `W⁰[f; x](r)` only records the local-norm inequality. -/

/-- Helper for Proposition 5.0.15: if a continuous linear operator is positive, enlarging the
scalar factor preserves the Loewner order between its scalar multiples. -/
private lemma positive_operator_smul_mono
    {A : E →L[ℝ] E} (hA : 0 ≤ A) {a b : ℝ} (hab : a ≤ b) :
    a • A ≤ b • A := by
  -- Rewrite the comparison as positivity of the difference scalar multiple `(b - a) • A`.
  have hba : 0 ≤ b - a := by
    linarith
  have hAPos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).1 hA
  rw [ContinuousLinearMap.le_def]
  simpa [sub_smul] using hAPos.smul_of_nonneg hba

/-- Helper for Proposition 5.0.15: the open-Dikin hypothesis already forces the exact local
displacement radius `‖y - x‖[f; x]` to lie below the reciprocal self-concordance constant. -/
private lemma exact_local_radius_lt_inv_constant
    {Mf : NNReal} {f : E → ℝ} {x y : E} {r : ℝ}
    (hxy : y ∈ W⁰[f; x](r)) (hr : r < 1 / (Mf : ℝ)) :
    ‖y - x‖[f; x] < 1 / (Mf : ℝ) := by
  -- Unpack the open-Dikin condition and compose it with the ambient radius hypothesis.
  have hρ_lt_r : ‖y - x‖[f; x] < r := by
    simpa using (mem_openDikinEllipsoid_iff f x y r).1 hxy
  exact hρ_lt_r.trans hr

/-- Helper for Proposition 5.0.15: the exact Dikin factor `1 - M_f ‖y - x‖[f; x]` is positive
under the open-Dikin hypothesis. -/
private lemma exact_local_radius_factor_pos
    {Mf : NNReal} {f : E → ℝ} {x y : E} {r : ℝ}
    (hxy : y ∈ W⁰[f; x](r)) (hr : r < 1 / (Mf : ℝ)) :
    0 < 1 - (Mf : ℝ) * ‖y - x‖[f; x] := by
  -- First isolate the exact-radius inequality forced by the Dikin-step hypothesis.
  have hρ_lt_inv : ‖y - x‖[f; x] < 1 / (Mf : ℝ) :=
    exact_local_radius_lt_inv_constant hxy hr
  have hρ_nonneg : 0 ≤ ‖y - x‖[f; x] := hessianLocalNorm_nonneg f x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
  have hMf_pos : 0 < (Mf : ℝ) := by
    -- If `Mf = 0`, then the strict reciprocal-radius inequality would force a negative local norm.
    by_contra hMf_nonpos
    have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
    have hρ_lt_zero : ‖y - x‖[f; x] < 0 := by
      simpa [hMf_eq_zero] using hρ_lt_inv
    exact not_lt_of_ge hρ_nonneg hρ_lt_zero
  have hmul_lt_one : (Mf : ℝ) * ‖y - x‖[f; x] < 1 := by
    -- Multiplying the exact-radius estimate by the positive constant `Mf` yields the textbook
    -- admissibility inequality `M_f ‖y - x‖[f; x] < 1`.
    have hmul : ‖y - x‖[f; x] * (Mf : ℝ) < 1 := by
      exact (lt_div_iff₀ hMf_pos).1 hρ_lt_inv
    simpa [mul_comm] using hmul
  linarith

/-- Helper for Proposition 5.0.15: at a feasible base point, the local Hessian norm is
homogeneous in the direction argument. -/
private lemma hessianLocalNorm_smul_eq_abs
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {z u : E} (hz : z ∈ dom) (a : ℝ) :
    ‖a • u‖[f; z] = |a| * ‖u‖[f; z] := by
  -- Rewrite the scaled quadratic form and take square roots using Hessian semidefiniteness.
  have hquad : 0 ≤ inner ℝ u (hessian f z u) := hself.hessian_posSemidef hz u
  calc
    ‖a • u‖[f; z] = Real.sqrt ((a * a) * inner ℝ u (hessian f z u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f z u)) * Real.sqrt (a * a) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = |a| * ‖u‖[f; z] := by
      rw [show a * a = a ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, hessianLocalNorm_def]
      ring

section AssociatedUnivariateFunctionBridge

variable {dom : Set E} {f : E → ℝ} {x h : E}

local notation "sliceDomain" => associatedUnivariateFunctionDomain dom f x h
local notation "reciprocalLocalNormSlice" =>
  directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h

/-- Helper for Proposition 5.0.15: a `C²` real-valued function has a differentiable gradient
because the gradient is the Fréchet derivative transported through the Riesz isomorphism. -/
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

/-- Helper for Proposition 5.0.15: the affine line restriction `directionalSlice f x h` is `C³`
at `t` whenever `x + t • h ∈ dom`. -/
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

/-- Helper for Proposition 5.0.15: shifting the base point of the line slice rewrites the second
iterated derivative as the Hessian quadratic form at the shifted point. -/
private theorem directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    {s : ℝ} (hs : x + s • h ∈ dom) :
    iteratedDeriv 2 (directionalSlice f x h) s =
      inner ℝ h ((fderiv ℝ (∇ f) (x + s • h)) h) := by
  -- Translate the slice to the origin and identify its second derivative with the Hessian
  -- quadratic form.
  have hfAt : ContDiffAt ℝ 3 f (x + s • h) := hcont.contDiffAt (hdom_open.mem_nhds hs)
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
          exact secondDirectionalDerivative_eq_hessian_quadratic_form (hfAt.of_le (by norm_num))
    _ = inner ℝ h ((fderiv ℝ (∇ f) (x + s • h)) h) := by
          simp [hessian]

/-- Helper for Proposition 5.0.15: shifting the base point of the line slice rewrites the third
iterated derivative as the chapter owner `thirdDirectionalDerivative` at the shifted point. -/
private theorem directionalSlice_iteratedDeriv_three_eq_thirdDirectionalDerivative
    (s : ℝ) :
    iteratedDeriv 3 (directionalSlice f x h) s =
      thirdDirectionalDerivative f (x + s • h) h := by
  -- The same translation identity works at third order.
  have hshift :
      (fun z : ℝ ↦ directionalSlice f x h (s + z)) =
        directionalSlice f (x + s • h) h := by
    funext z
    simp [directionalSlice, add_smul, add_assoc]
  calc
    iteratedDeriv 3 (directionalSlice f x h) s
      = iteratedDeriv 3 (fun z : ℝ ↦ directionalSlice f x h (s + z)) 0 := by
          simpa using congrArg (fun k : ℝ → ℝ ↦ k 0)
            (iteratedDeriv_comp_const_add 3 (directionalSlice f x h) s).symm
    _ = thirdDirectionalDerivative f (x + s • h) h := by
          rw [hshift, thirdDirectionalDerivative]

/-- Helper for Proposition 5.0.15: the natural slice domain is a neighborhood of each of its
points, because both the ambient-domain condition and the local-norm positivity condition are
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
    -- Continuity of the second slice derivative preserves positivity near `t`.
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

/-- Helper for Proposition 5.0.15: the canonical reciprocal local-norm slice has the displayed
within-derivative formula on its natural positivity domain. -/
private theorem associatedUnivariateFunction_hasDerivWithinAt
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    {t : ℝ} (ht : t ∈ sliceDomain) :
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
    -- A `C³` slice has a differentiable second iterated derivative at `t`.
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
        directionalSlice_iteratedDeriv_three_eq_thirdDirectionalDerivative t
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
    -- Then differentiate the reciprocal to obtain the reciprocal local-norm derivative.
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
  have hcoeff :
      (-(thirdDirectionalDerivative f (x + t • h) h / (2 * Real.sqrt (q t))) /
          (Real.sqrt (q t)) ^ (2 : ℕ)) =
        (-(thirdDirectionalDerivative f (x + t • h) h /
            (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ)))) := by
    -- Rewrite the coefficient from the auxiliary `q` notation back to the chapter owners.
    have hsqrt_eq : Real.sqrt (q t) = ‖h‖[f; x + t • h] := by
      calc
        Real.sqrt (q t)
          = Real.sqrt (inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h)) := by
              congr 1
              exact
                directionalSlice_iteratedDeriv_two_eq_hessian_quadratic_form hdom_open hcont ht_dom
        _ = ‖h‖[f; x + t • h] := by
              simpa [hessianLocalNorm_def, hessian]
    rw [hsqrt_eq]
    field_simp [hnorm_ne]
  exact hrewritten.congr_deriv hcoeff

/-- Helper for Proposition 5.0.15: the derivative of the reciprocal local-norm slice is bounded
in absolute value by `M_f` on its natural domain. -/
private theorem abs_derivWithin_associatedUnivariateFunction_le
    {Mf : NNReal}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {t : ℝ} (ht : t ∈ sliceDomain) :
    |derivWithin reciprocalLocalNormSlice sliceDomain t| ≤ (Mf : ℝ) := by
  -- Differentiate the reciprocal local-norm slice using the explicit local bridge formula.
  have hderiv :
      HasDerivWithinAt
        reciprocalLocalNormSlice
        (-(thirdDirectionalDerivative f (x + t • h) h /
            (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ))))
        sliceDomain
        t :=
    associatedUnivariateFunction_hasDerivWithinAt hself.isOpen_domain hself.contDiffOn ht
  have hunique : UniqueDiffWithinAt ℝ sliceDomain t := by
    -- The natural slice domain is a neighborhood of `t`, so derivatives within it are unique.
    exact uniqueDiffWithinAt_of_mem_nhds
      (associatedUnivariateFunctionDomain_mem_nhds hself.isOpen_domain hself.contDiffOn ht)
  rw [hderiv.derivWithin hunique]
  -- The self-concordance bound is exactly the absolute-value estimate for the explicit derivative.
  have ht_pos : 0 < ‖h‖[f; x + t • h] :=
    (mem_associatedUnivariateFunctionDomain_iff dom f x h t).1 ht |>.2
  have htwo_abs : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  have hnorm_abs : |‖h‖[f; x + t • h]| = ‖h‖[f; x + t • h] := abs_of_pos ht_pos
  have hbound :
      |thirdDirectionalDerivative f (x + t • h) h| /
          (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ)) ≤ (Mf : ℝ) := by
    rcases (mem_associatedUnivariateFunctionDomain_iff dom f x h t).1 ht with ⟨ht_dom, _⟩
    have hden_pos : 0 < 2 * ‖h‖[f; x + t • h] ^ (3 : ℕ) := by
      have hpow_pos : 0 < ‖h‖[f; x + t • h] ^ (3 : ℕ) := by
        positivity
      positivity
    refine (div_le_iff₀ hden_pos).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hself.third_deriv_bound ht_dom h
  simpa [abs_neg, abs_div, abs_mul, htwo_abs, hnorm_abs] using hbound

end AssociatedUnivariateFunctionBridge

/-- Helper for Proposition 5.0.15: every point of the segment from `x` to `y` stays in the raw
open Dikin ellipsoid of reciprocal radius around `x`. This is the source-faithful radius control
that remains before recovering domain membership. -/
private lemma segment_point_mem_openDikinEllipsoid_inv_constant
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E} {r t : ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) (hx : x ∈ dom)
    (hr : r < 1 / (Mf : ℝ)) (hxy : y ∈ W⁰[f; x](r))
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
  -- Scale the exact displacement norm by `|t| ≤ 1` and then use `‖y - x‖[f; x] < r < 1 / M_f`.
  have hρ_lt_r : ‖y - x‖[f; x] < r := by
    simpa using (mem_openDikinEllipsoid_iff f x y r).1 hxy
  have hρ_nonneg : 0 ≤ ‖y - x‖[f; x] := hessianLocalNorm_nonneg f x (y - x)
  have h_abs_t_le : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hscaled_lt_r : |t| * ‖y - x‖[f; x] < r := by
    have hscaled_le :
        |t| * ‖y - x‖[f; x] ≤ 1 * ‖y - x‖[f; x] :=
      mul_le_mul_of_nonneg_right h_abs_t_le hρ_nonneg
    exact lt_of_le_of_lt hscaled_le (by simpa using hρ_lt_r)
  rw [mem_openDikinEllipsoid_iff]
  calc
    ‖(x + t • (y - x)) - x‖[f; x] = ‖t • (y - x)‖[f; x] := by
      simp
    _ = |t| * ‖y - x‖[f; x] := hessianLocalNorm_smul_eq_abs hself hx t
    _ < 1 / (Mf : ℝ) := hscaled_lt_r.trans hr

/-- Helper for Proposition 5.0.15: the exact Dikin factor stays positive at every segment
parameter `t ∈ [0, 1]`. -/
private lemma segment_exact_local_radius_factor_pos
    {Mf : NNReal} {f : E → ℝ} {x y : E} {r t : ℝ}
    (hxy : y ∈ W⁰[f; x](r)) (hr : r < 1 / (Mf : ℝ))
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - t * (Mf : ℝ) * ‖y - x‖[f; x] := by
  -- Compare `t * M_f * ‖y - x‖[f; x]` with the endpoint value at `t = 1`.
  have hfactor_pos :
      0 < 1 - (Mf : ℝ) * ‖y - x‖[f; x] :=
    exact_local_radius_factor_pos hxy hr
  have hρ_nonneg : 0 ≤ ‖y - x‖[f; x] := hessianLocalNorm_nonneg f x (y - x)
  have hMfρ_nonneg : 0 ≤ (Mf : ℝ) * ‖y - x‖[f; x] := mul_nonneg Mf.2 hρ_nonneg
  have hmul_le :
      t * (Mf : ℝ) * ‖y - x‖[f; x] ≤ (Mf : ℝ) * ‖y - x‖[f; x] := by
    have hmul_le' :
        t * ((Mf : ℝ) * ‖y - x‖[f; x]) ≤ 1 * ((Mf : ℝ) * ‖y - x‖[f; x]) :=
      mul_le_mul_of_nonneg_right ht.2 hMfρ_nonneg
    simpa [mul_assoc] using hmul_le'
  linarith

/-- Helper for Proposition 5.0.15: once the segment argument supplies quadratic-form bounds in
every direction and the endpoint Hessians are positive, the corresponding Loewner inequalities
follow by checking positivity of the operator differences on diagonal pairings. -/
private lemma loewner_bounds_of_scalarized_quadratic_form_bounds
    {f : E → ℝ} {x y : E} {coeff : ℝ}
    (hxPos : (hessian f x).IsPositive) (hyPos : (hessian f y).IsPositive)
    (hlower :
      ∀ v : E, coeff * inner ℝ v (hessian f x v) ≤ inner ℝ v (hessian f y v))
    (hupper :
      ∀ v : E, inner ℝ v (hessian f y v) ≤ coeff⁻¹ * inner ℝ v (hessian f x v)) :
    coeff • hessian f x ≤ hessian f y ∧
      hessian f y ≤ coeff⁻¹ • hessian f x := by
  constructor
  · -- Rewrite the lower Loewner claim as positivity of `∇²f(y) - coeff • ∇²f(x)`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hySymm : inner ℝ (hessian f y u) v = inner ℝ u (hessian f y v) := by
        simpa using hyPos.isSymmetric u v
      have hxSymm : inner ℝ (hessian f x u) v = inner ℝ u (hessian f x v) := by
        simpa using hxPos.isSymmetric u v
      calc
        inner ℝ ((hessian f y - coeff • hessian f x) u) v =
            inner ℝ (hessian f y u) v - coeff * inner ℝ (hessian f x u) v := by
              simp [inner_sub_left, inner_smul_left]
        _ =
            inner ℝ u (hessian f y v) - coeff * inner ℝ u (hessian f x v) := by
              rw [hySymm, hxSymm]
        _ = inner ℝ u ((hessian f y - coeff • hessian f x) v) := by
              simp [inner_sub_right, inner_smul_right]
    · intro u
      have hySymm : inner ℝ (hessian f y u) u = inner ℝ u (hessian f y u) := by
        simpa using hyPos.isSymmetric u u
      have hxSymm : inner ℝ (hessian f x u) u = inner ℝ u (hessian f x u) := by
        simpa using hxPos.isSymmetric u u
      have hrewrite :
          inner ℝ ((hessian f y - coeff • hessian f x) u) u =
            inner ℝ u (hessian f y u) - coeff * inner ℝ u (hessian f x u) := by
        calc
          inner ℝ ((hessian f y - coeff • hessian f x) u) u
              = inner ℝ (hessian f y u) u - coeff * inner ℝ (hessian f x u) u := by
                  simp [inner_sub_left, inner_smul_left]
          _ = inner ℝ u (hessian f y u) - coeff * inner ℝ u (hessian f x u) := by
                  rw [hySymm, hxSymm]
      rw [hrewrite]
      linarith [hlower u]
  · -- Rewrite the upper Loewner claim as positivity of `coeff⁻¹ • ∇²f(x) - ∇²f(y)`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hxSymm : inner ℝ (hessian f x u) v = inner ℝ u (hessian f x v) := by
        simpa using hxPos.isSymmetric u v
      have hySymm : inner ℝ (hessian f y u) v = inner ℝ u (hessian f y v) := by
        simpa using hyPos.isSymmetric u v
      calc
        inner ℝ ((coeff⁻¹ • hessian f x - hessian f y) u) v =
            coeff⁻¹ * inner ℝ (hessian f x u) v - inner ℝ (hessian f y u) v := by
              simp [inner_sub_left, inner_smul_left]
        _ =
            coeff⁻¹ * inner ℝ u (hessian f x v) - inner ℝ u (hessian f y v) := by
              rw [hxSymm, hySymm]
        _ = inner ℝ u ((coeff⁻¹ • hessian f x - hessian f y) v) := by
              simp [inner_sub_right, inner_smul_right]
    · intro u
      have hxSymm : inner ℝ (hessian f x u) u = inner ℝ u (hessian f x u) := by
        simpa using hxPos.isSymmetric u u
      have hySymm : inner ℝ (hessian f y u) u = inner ℝ u (hessian f y u) := by
        simpa using hyPos.isSymmetric u u
      have hrewrite :
          inner ℝ ((coeff⁻¹ • hessian f x - hessian f y) u) u =
            coeff⁻¹ * inner ℝ u (hessian f x u) - inner ℝ u (hessian f y u) := by
        calc
          inner ℝ ((coeff⁻¹ • hessian f x - hessian f y) u) u
              = coeff⁻¹ * inner ℝ (hessian f x u) u - inner ℝ (hessian f y u) u := by
                  simp [inner_sub_left, inner_smul_left]
          _ = coeff⁻¹ * inner ℝ u (hessian f x u) - inner ℝ u (hessian f y u) := by
                  rw [hxSymm, hySymm]
      rw [hrewrite]
      linarith [hupper u]

/-- Helper for Proposition 5.0.15: every affine parameter `t ∈ [0, 1]` produces the
corresponding point `x + t • (y - x)` on `segment ℝ x y`. -/
private lemma segment_point_mem_segment
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine interpolation point into the canonical line-map description of the
  -- segment.
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Proposition 5.0.15: the affine segment parameterization has derivative equal to
its direction. -/
private lemma affine_segment_hasDerivAt
    {x d : E} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the fixed base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Proposition 5.0.15: a pointwise `C³` hypothesis makes the Hessian field
Fréchet-differentiable as an operator-valued map. -/
private lemma hessian_hasFDerivAt_of_contDiffAt
    {f : E → ℝ} {z : E} (hcontAt : ContDiffAt ℝ 3 f z) :
    HasFDerivAt (hessian f) (fderiv ℝ (hessian f) z) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) z := by
    -- First differentiate `f` once and keep two derivatives in reserve.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ f) z := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp z hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian f) z := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the requested Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Proposition 5.0.15: the scalarized Hessian quadratic form
`s ↦ inner ℝ v (hessian f (x + s • (y - x)) v)` differentiates to the mixed Hessian-direction
pairing. -/
private lemma segment_scalarized_hessian_hasDerivAt
    {f : E → ℝ} {x y v : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    {t : ℝ}
    (hcontAt : ContDiffAt ℝ 3 f (z t)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ v (hessian f (z s) v))
      (inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v)) t := by
  have hzLine : HasDerivAt z (y - x) t := by
    -- Specialize the affine-line derivative to the segment parameterization.
    subst hz
    simpa using affine_segment_hasDerivAt (x := x) (d := y - x) t
  have hhessianDeriv :
      HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (z t)) (z t) :=
    hessian_hasFDerivAt_of_contDiffAt hcontAt
  have happly :
      HasDerivAt (fun s : ℝ ↦ hessian f (z s) v)
        ((fderiv ℝ (hessian f) (z t) (y - x)) v) t := by
    -- Differentiate the Hessian field along the segment and then evaluate it on the fixed
    -- direction `v`.
    have happlyF :
        HasFDerivAt (fun w : E ↦ hessian f w v)
          ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (hessian f) (z t))) (z t) := by
      exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp (z t) hhessianDeriv
    simpa using happlyF.comp_hasDerivAt t hzLine
  have hinnerF :
      HasFDerivAt (fun w : E ↦ inner ℝ v w) ((innerSL ℝ) v) (hessian f (z t) v) := by
    -- Postcompose with the linear functional `w ↦ ⟪v, w⟫`.
    simpa using ((innerSL ℝ) v).hasFDerivAt
  simpa using hinnerF.comp_hasDerivAt t happly

/-- Helper for Proposition 5.0.15: the mixed Hessian-direction pairing is the `(d,v,v)` slot of
the third iterated derivative. -/
private lemma pointwise_mixed_hessian_pairing_eq_iteratedFDeriv
    {f : E → ℝ} {z d v : E}
    (hcontAt : ContDiffAt ℝ 3 f z) :
    inner ℝ v ((fderiv ℝ (hessian f) z d) v) = iteratedFDeriv ℝ 3 f z ![d, v, v] := by
  let line : ℝ → E := fun s ↦ z + s • d
  let φ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (line s) v)
  let ψ : ℝ → ℝ := fun s ↦ iteratedFDeriv ℝ 2 f (line s) ![v, v]
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hzs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  have hEqOn : ∀ w ∈ s, inner ℝ v (hessian f w v) = iteratedFDeriv ℝ 2 f w ![v, v] := by
    intro w hw
    -- On a local `C³` neighborhood, the Hessian quadratic form is exactly the second iterated
    -- derivative evaluated on the repeated direction `v`.
    have hw_cont : ContDiffAt ℝ 3 f w := hs_contOn.contDiffAt (hs_open.mem_nhds hw)
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) w := by
      exact hw_cont.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) w := by
      exact hfderiv_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hgrad_hasFDeriv :
        HasFDerivAt (∇ f)
          (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
            (fderiv ℝ (fderiv ℝ f) w)) w := by
      simpa [gradient] using
        (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.comp w
          hfderiv_diff.hasFDerivAt)
    rw [hessian, hgrad_hasFDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [real_inner_comm]
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
            ((fderiv ℝ (fderiv ℝ f) w) v)) v
          = ((fderiv ℝ (fderiv ℝ f) w) v) v := by
              simpa using
                (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v)
                  (y := ((fderiv ℝ (fderiv ℝ f) w) v)))
      _ = iteratedFDeriv ℝ 2 f w ![v, v] := by
            simpa [iteratedFDeriv_two_apply]
  have hline_mem : ∀ᶠ t in nhds (0 : ℝ), line t ∈ s := by
    let hline0 : ContinuousAt line 0 :=
      (affine_segment_hasDerivAt (x := z) (d := d) 0).continuousAt
    exact hline0.tendsto.eventually (hs_open.mem_nhds (by simpa [line] using hzs))
  have hEq : φ =ᶠ[nhds (0 : ℝ)] ψ := by
    filter_upwards [hline_mem] with t ht
    simp [φ, ψ, line, hEqOn _ ht]
  have hφ :
      HasDerivAt φ (inner ℝ v ((fderiv ℝ (hessian f) z d) v)) 0 := by
    have hzLine : HasDerivAt line d 0 := by
      simpa [line] using affine_segment_hasDerivAt (x := z) (d := d) 0
    have hhessianDeriv :
        HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (line 0)) (line 0) := by
      simpa [line] using hessian_hasFDerivAt_of_contDiffAt (f := f) (z := z) hcontAt
    have happly :
        HasDerivAt (fun t : ℝ ↦ hessian f (line t) v)
          ((fderiv ℝ (hessian f) (line 0) d) v) 0 := by
      -- Differentiate the operator-valued Hessian map along the affine line and then evaluate it
      -- on `v`.
      have happlyF :
          HasFDerivAt (fun w : E ↦ hessian f w v)
            ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (hessian f) (line 0))) (line 0) := by
        exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp (line 0) hhessianDeriv
      simpa using happlyF.comp_hasDerivAt 0 hzLine
    have hinnerF :
        HasFDerivAt (fun w : E ↦ inner ℝ v w) ((innerSL ℝ) v) (hessian f (line 0) v) := by
      -- The scalar pairing `φ` is the composition of the Hessian line with the fixed inner
      -- product against `v`.
      simpa using ((innerSL ℝ) v).hasFDerivAt
    simpa [φ, line] using hinnerF.comp_hasDerivAt 0 happly
  have hiter2_C1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 f) z := by
    exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
  have hiter2_deriv :
      HasFDerivAt (iteratedFDeriv ℝ 2 f) (fderiv ℝ (iteratedFDeriv ℝ 2 f) z) z := by
    exact (hiter2_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hψ :
      HasDerivAt ψ (((fderiv ℝ (iteratedFDeriv ℝ 2 f) z) d) ![v, v]) 0 := by
    have hline0 : HasDerivAt line d 0 := by
      simpa [line] using affine_segment_hasDerivAt (x := z) (d := d) 0
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ iteratedFDeriv ℝ 2 f (line t))
          ((fderiv ℝ (iteratedFDeriv ℝ 2 f) z) d) 0 := by
      simpa [line] using
        hiter2_deriv.comp_hasDerivAt_of_eq 0 hline0 (by simp [line])
    -- Evaluate the derivative of the bilinear iterated derivative on the repeated direction `v`.
    simpa [ψ] using
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![v, v]).hasFDerivAt.comp_hasDerivAt 0
        hcomp)
  have hψ_from_φ : HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) z d) v)) 0 :=
    hφ.congr_of_eventuallyEq hEq.symm
  have hsame :
      inner ℝ v ((fderiv ℝ (hessian f) z d) v) =
        ((fderiv ℝ (iteratedFDeriv ℝ 2 f) z) d) ![v, v] :=
    hψ_from_φ.unique hψ
  -- Rewrite the derivative of the second iterated derivative back to the canonical third-order
  -- owner.
  simpa [iteratedFDeriv_succ_apply_left] using hsame

/-- Helper for Proposition 5.0.15: once the segment from `x` to `y` stays in `dom`, the
segment-local Hessian comparison theorem yields the exact-radius endpoint quadratic-form bounds. -/
private lemma scalarizedHessianEndpointBounds_of_segmentControl
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    {x y : E}
    (hdom_open : IsOpen dom)
    (hcontOn : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    (hpsd :
      ∀ ⦃z : E⦄, z ∈ segment ℝ x y → (hessian f z).IsPositive)
    (hthird :
      ∀ ⦃z : E⦄ (_hz : z ∈ segment ℝ x y) (u : E),
        |thirdDirectionalDerivative f z u| ≤
          2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    (hyDikin : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    (∀ v : E,
      ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤
        inner ℝ v (hessian f y v)) ∧
    (∀ v : E,
        inner ℝ v (hessian f y v) ≤
        ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v)) := by
  -- Apply the segment-local Hessian comparison theorem and then test the operator inequalities on
  -- each direction `v`.
  have hcore :
      let r := ‖y - x‖[f; x]
      ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
        hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := by
    exact
      hessian_loewner_bounds_along_segment
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hdom_open hcontOn hsegment hpsd hthird hyDikin
  rcases hcore with ⟨hlower, hupper⟩
  constructor
  · intro v
    rw [ContinuousLinearMap.le_def] at hlower
    have hdiag : 0 ≤
        inner ℝ v
          ((hessian f y -
              ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ)) • hessian f x) v) :=
      hlower.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiag
  · intro v
    rw [ContinuousLinearMap.le_def] at hupper
    have hdiag : 0 ≤
        inner ℝ v
          ((((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x - hessian f y) v) :=
      hupper.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiag

-- Semantic recall check: `lean_leansearch` produced no relevant Dikin/self-concordance Hessian
-- comparison owner, so this file stays on the local Chapter 5 API.
/-- Helper for Proposition 5.0.15: with `y ∈ dom` supplied explicitly, the segment ODE argument
yields the scalarized Hessian quadratic-form bounds at the exact local radius. -/
private lemma scalarized_hessian_quadratic_bounds_along_segment
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} {r : ℝ} (hx : x ∈ dom) (hy : y ∈ dom) (hr : r < 1 / (Mf : ℝ))
    (hxy : y ∈ W⁰[f; x](r)) :
    (∀ v : E,
      ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤
        inner ℝ v (hessian f y v)) ∧
    (∀ v : E,
      inner ℝ v (hessian f y v) ≤
        ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v)) := by
  -- Work on the affine segment `z t = x + t • (y - x)`, where convexity of `dom` supplies the
  -- domain membership needed to apply the self-concordance hypotheses pointwise.
  have hsegment : segment ℝ x y ⊆ dom := by
    exact hself.convex_domain.segment_subset hx hy
  have hyDikin : y ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
    rw [mem_openDikinEllipsoid_iff]
    exact exact_local_radius_lt_inv_constant hxy hr
  -- Reuse the later segment-local comparison theorem and then scalarize it on each direction.
  exact
    scalarizedHessianEndpointBounds_of_segmentControl
      hself.isOpen_domain hself.contDiffOn hsegment
      (by
        intro z hz
        exact hself.hessian_isPositive (hsegment hz))
      (by
        intro z hz u
        exact hself.third_deriv_bound (hsegment hz) u)
      hyDikin

-- Proof sketch: compare first at the exact displacement radius `ρ = ‖y - x‖[f; x]`, where the
-- source ODE argument naturally lands, and only then weaken from `ρ` to the user-supplied `r`.
/-- Reusable companion to Proposition 5.0.15: the self-concordant Hessian comparison at the exact
local displacement radius `‖y - x‖[f; x]`, with the domain-membership half of the textbook Dikin
condition carried explicitly because `W⁰[f; x](r)` only records the local-norm inequality. -/
lemma hessian_loewner_bounds_of_exact_local_radius
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} {r : ℝ} (hx : x ∈ dom) (hy : y ∈ dom) (hr : r < 1 / (Mf : ℝ))
    (hxy : y ∈ W⁰[f; x](r)) :
    ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x := by
  -- Reassemble the already-established scalar quadratic-form bounds into operator inequalities.
  have hxPos : (hessian f x).IsPositive := hself.hessian_isPositive hx
  have hyPos : (hessian f y).IsPositive := hself.hessian_isPositive hy
  rcases scalarized_hessian_quadratic_bounds_along_segment hself hx hy hr hxy with
    ⟨hlower, hupper⟩
  simpa using
    loewner_bounds_of_scalarized_quadratic_form_bounds
      (f := f)
      (x := x)
      (y := y)
      (coeff := ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ)))
      hxPos hyPos hlower hupper

-- Proof sketch: for a fixed direction `v`, apply the one-dimensional self-concordance estimate
-- along the segment from `x` to `y` to the univariate function obtained by restricting the
-- Hessian quadratic form in the direction `v`. The Dikin-radius bound
-- `hessianLocalNorm f x (y - x) < r < 1 / M_f` then yields the factor `(1 - M_f r)^2` and its
-- reciprocal uniformly in `v`, which is exactly the Loewner-order comparison of the intrinsic
-- Hessian operators at `x` and `y`. The source-side Dikin ellipsoid membership
-- `y ∈ W(x; r) = {z ∈ dom f : ‖z - x‖_x < r}` is rendered here by the pair of hypotheses
-- `hy : y ∈ dom` and `hxy : y ∈ W⁰[f; x](r)`.
/-- Proposition 5.0.15: if `f` is self-concordant on `dom` with parameter `M_f`, `x ∈ dom`,
`y ∈ dom f`, `r < 1 / M_f`, and `‖y - x‖_x < r` (encoded here as `hxy : y ∈ W⁰[f; x](r)`), then
the Hessians at `x` and `y` are comparable in Loewner order by the factors `(1 - M_f r)^2` and
`(1 - M_f r)⁻²`. The explicit hypothesis `hy : y ∈ dom` supplies the domain-membership half of
the textbook Dikin ellipsoid condition `y ∈ W(x; r)`. -/
theorem hessian_loewner_bounds_of_mem_openDikinEllipsoid
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} {r : ℝ} (hx : x ∈ dom) (hy : y ∈ dom) (hr : r < 1 / (Mf : ℝ))
    (hxy : y ∈ W⁰[f; x](r)) :
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := by
  -- First compare at the exact local radius `‖y - x‖[f; x]`, then weaken to the user radius `r`.
  rcases hessian_loewner_bounds_of_exact_local_radius hself hx hy hr hxy with
    ⟨hexact_lower, hexact_upper⟩
  have hHx_nonneg : 0 ≤ hessian f x := by
    exact
      (ContinuousLinearMap.nonneg_iff_isPositive (hessian f x)).2
        (hself.hessian_isPositive hx)
  have hρ_lt_r : ‖y - x‖[f; x] < r := by
    simpa using (mem_openDikinEllipsoid_iff f x y r).1 hxy
  have hρ_nonneg : 0 ≤ ‖y - x‖[f; x] := hessianLocalNorm_nonneg f x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
  have hMf_pos : 0 < (Mf : ℝ) := by
    -- The Dikin step forces `Mf > 0`; otherwise `r < 1 / Mf` would contradict `ρ < r`.
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr
    exact not_lt_of_ge (le_trans hρ_nonneg (le_of_lt hρ_lt_r)) hr_neg
  have hr_factor_pos : 0 < 1 - (Mf : ℝ) * r := by
    have hmul_lt_one : (Mf : ℝ) * r < 1 := by
      simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hr
    linarith
  have hρ_factor_pos : 0 < 1 - (Mf : ℝ) * ‖y - x‖[f; x] :=
    exact_local_radius_factor_pos hxy hr
  have hcoeff_le :
      ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) ≤
        ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ)) := by
    have hbase_le :
        1 - (Mf : ℝ) * r ≤ 1 - (Mf : ℝ) * ‖y - x‖[f; x] := by
      nlinarith
    exact pow_le_pow_left₀ (le_of_lt hr_factor_pos) hbase_le 2
  have hcoeff_inv_le :
      ((1 - (Mf : ℝ) * ‖y - x‖[f; x]) ^ (2 : ℕ))⁻¹ ≤
        ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ := by
    have hcoeff_pos : 0 < ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) := by positivity
    simpa [one_div] using one_div_le_one_div_of_le hcoeff_pos hcoeff_le
  constructor
  · -- Enlarge the scalar factor on the positive operator `hessian f x`.
    exact le_trans (positive_operator_smul_mono hHx_nonneg hcoeff_le) hexact_lower
  · -- The inverse factors reverse in the same monotone way.
    exact le_trans hexact_upper (positive_operator_smul_mono hHx_nonneg hcoeff_inv_le)

end IsSelfConcordantOnWith

end
