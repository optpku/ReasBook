/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_13
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter Set
open scoped Topology

section Theorem1314

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {S : Set E} {f : E → ℝ}

-- The textbook states these criteria for nonempty open convex sets, but nonemptiness is
-- redundant for the Lean statements below.

/-- Helper for Chapter01 Theorem 1.3.14: the scalar second derivative of a line restriction
is the Hessian quadratic form in the line direction. -/
lemma deriv2_lineMap_eq_iteratedFDeriv_diag
    (hS_open : IsOpen S) (hC2 : ContDiffOn ℝ 2 f S)
    {x y : E} {I : Set ℝ}
    (hmem : ∀ t ∈ I, AffineMap.lineMap x y t ∈ S)
    {t : ℝ} (ht : t ∈ I) :
    (deriv^[2]) (fun s : ℝ ↦ f (AffineMap.lineMap x y s)) t =
      (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] := by
  let φ : ℝ → E := AffineMap.lineMap x y
  have hy : φ t ∈ S := hmem t ht
  have hfAt : ContDiffAt ℝ 2 f (φ t) :=
    hC2.contDiffAt (hS_open.mem_nhds hy)
  have hφAt : ContDiffAt ℝ 2 φ t := by
    simpa [φ] using
      (AffineMap.contDiff_lineMap x y : ContDiff ℝ 2 (AffineMap.lineMap x y : ℝ → E)).contDiffAt
  -- Compose the line map with `f`, then evaluate the second one-dimensional derivative.
  rw [← iteratedDeriv_eq_iterate]
  calc
    iteratedDeriv 2 (fun s ↦ f (AffineMap.lineMap x y s)) t
        = iteratedDeriv 2 (f ∘ φ) t := by
            rfl
    _ = (iteratedFDeriv ℝ 2 f (φ t)) (fun _ ↦ deriv φ t) +
          fderiv ℝ f (φ t) (iteratedDeriv 2 φ t) := by
            simpa [φ, Function.comp] using iteratedDeriv_vcomp_two (g := f) (f := φ) hfAt hφAt
    _ = (iteratedFDeriv ℝ 2 f (φ t)) ![y - x, y - x] +
          fderiv ℝ f (φ t) (iteratedDeriv 2 φ t) := by
            have hφDeriv : deriv φ t = y - x := by
              simpa [φ] using
                (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).deriv
            have hvec : (fun _ : Fin 2 => y - x) = ![y - x, y - x] := by
              funext i
              fin_cases i <;> rfl
            simp [hφDeriv, hvec]
    _ = (iteratedFDeriv ℝ 2 f (φ t)) ![y - x, y - x] := by
            have hφDerivFun : deriv φ = fun _ ↦ y - x := by
              funext s
              simpa [φ] using
                (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := s)).deriv
            have hφTwo : iteratedDeriv 2 φ t = 0 := by
              rw [iteratedDeriv_succ, iteratedDeriv_one, hφDerivFun]
              simp
            rw [hφTwo, map_zero, add_zero]

/-- Helper for Chapter01 Theorem 1.3.14: the scalar quadratic `(c / 2) * t^2`
has constant second derivative `c`. -/
lemma deriv2_half_mul_sq (c t : ℝ) :
    (deriv^[2]) (fun s : ℝ ↦ (c / 2) * s ^ (2 : ℕ)) t = c := by
  have hpow : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ (2 : ℕ)) t := by
    fun_prop
  -- Rewrite the second derivative through the iterated-derivative API for polynomials.
  rw [← iteratedDeriv_eq_iterate]
  calc
    iteratedDeriv 2 (fun s : ℝ ↦ (c / 2) * s ^ (2 : ℕ)) t
        = (c / 2) * iteratedDeriv 2 (fun s : ℝ ↦ s ^ (2 : ℕ)) t := by
            simpa using iteratedDeriv_const_mul (x := t) (n := 2) (c := c / 2) hpow
    _ = (c / 2) * (2 : ℝ) := by simp [iteratedDeriv_pow]
    _ = c := by ring

/-- Helper for Chapter01 Theorem 1.3.14: subtracting the scalar quadratic shift
lowers the line restriction's second derivative by the shift constant. -/
lemma deriv2_lineMap_sub_half_mul_sq_eq
    (hS_open : IsOpen S) (hC2 : ContDiffOn ℝ 2 f S)
    {x y : E} {I : Set ℝ}
    (hmem : ∀ t ∈ I, AffineMap.lineMap x y t ∈ S)
    {c t : ℝ} (ht : t ∈ I) :
    (deriv^[2]) (fun s : ℝ ↦
      f (AffineMap.lineMap x y s) - (c / 2) * s ^ (2 : ℕ)) t =
      (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] - c := by
  let g : ℝ → ℝ := fun s ↦ f (AffineMap.lineMap x y s)
  let q : ℝ → ℝ := fun s ↦ (c / 2) * s ^ (2 : ℕ)
  have hgAt : ContDiffAt ℝ 2 g t := by
    have hfAt : ContDiffAt ℝ 2 f (AffineMap.lineMap x y t) :=
      hC2.contDiffAt (hS_open.mem_nhds (hmem t ht))
    have hlineAt : ContDiffAt ℝ 2 (AffineMap.lineMap x y : ℝ → E) t := by
      simpa using
        (AffineMap.contDiff_lineMap x y : ContDiff ℝ 2 (AffineMap.lineMap x y : ℝ → E)).contDiffAt
    -- Compose the smooth line map with `f` to expose the iterated-derivative subtraction rule.
    change ContDiffAt ℝ 2 (f ∘ AffineMap.lineMap x y) t
    exact ContDiffAt.comp t hfAt hlineAt
  have hqAt : ContDiffAt ℝ 2 q t := by
    -- The quadratic correction is a polynomial, hence `C²`.
    fun_prop
  change (deriv^[2]) (g - q) t =
      (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] - c
  rw [← iteratedDeriv_eq_iterate]
  calc
    iteratedDeriv 2 (g - q) t = iteratedDeriv 2 g t - iteratedDeriv 2 q t := by
      simpa using iteratedDeriv_sub hgAt hqAt
    _ = (deriv^[2]) g t - (deriv^[2]) q t := by
      rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
    _ = (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] - c := by
      rw [show (deriv^[2]) g t =
          (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] by
            simpa [g] using deriv2_lineMap_eq_iteratedFDeriv_diag hS_open hC2 hmem ht]
      rw [show (deriv^[2]) q t = c by simpa [q] using deriv2_half_mul_sq c t]

/-- Helper for Chapter01 Theorem 1.3.14: on a symmetric interval around the origin,
convexity and differentiability of a scalar restriction force a nonnegative second derivative
at the base point. -/
lemma deriv2_nonneg_at_zero_of_convexOn_interval
    {δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (-δ) δ) g)
    (hdiff : ∀ t ∈ Set.Icc (-δ) δ, DifferentiableAt ℝ g t)
    (hddiff0 : DifferentiableAt ℝ (deriv g) 0) :
    0 ≤ (deriv^[2]) g 0 := by
  let I : Set ℝ := Set.Icc (-δ) δ
  have hmon : MonotoneOn (deriv g) I := by
    simpa [I] using hconv.monotoneOn_deriv (by simpa [I] using hdiff)
  have h0I : (0 : ℝ) ∈ I := by
    simp [I, hδ.le]
  have hacc : AccPt (0 : ℝ) (𝓟 I) := by
    rw [← uniqueDiffWithinAt_iff_accPt]
    exact (uniqueDiffOn_Icc (show -δ < δ by linarith)).uniqueDiffWithinAt h0I
  have hd2 : HasDerivWithinAt (deriv g) ((deriv^[2]) g 0) I 0 := by
    simpa [Function.iterate_succ_apply] using hddiff0.hasDerivAt.hasDerivWithinAt
  exact hd2.nonneg_of_monotoneOn hacc hmon

/-- Helper for Chapter01 Theorem 1.3.14: nonnegative Hessian quadratic form along every segment
implies the first-order supporting inequality. -/
lemma ge_gradient_inner_sub_of_iteratedFDeriv_nonneg
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S)
    (hNonneg : ∀ z ∈ S, ∀ v : E, 0 ≤ (iteratedFDeriv ℝ 2 f z) ![v, v])
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    f y ≥ f x + inner ℝ (gradient f x) (y - x) := by
  let I : Set ℝ := Set.Icc 0 1
  let g : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hmem : ∀ t ∈ I, AffineMap.lineMap x y t ∈ S := by
    intro t ht
    simpa [I] using hS_convex.lineMap_mem hx hy ht
  have hgAt : ∀ t ∈ I, ContDiffAt ℝ 2 g t := by
    intro t ht
    have hfAt : ContDiffAt ℝ 2 f (AffineMap.lineMap x y t) :=
      hC2.contDiffAt (hS_open.mem_nhds (hmem t ht))
    have hlineAt : ContDiffAt ℝ 2 (AffineMap.lineMap x y : ℝ → E) t := by
      simpa using
        (AffineMap.contDiff_lineMap x y : ContDiff ℝ 2 (AffineMap.lineMap x y : ℝ → E)).contDiffAt
    -- Every point of the segment sees the global `C²` scalar restriction.
    change ContDiffAt ℝ 2 (f ∘ AffineMap.lineMap x y) t
    exact ContDiffAt.comp t hfAt hlineAt
  have hgDiff : DifferentiableOn ℝ g I := by
    intro t ht
    exact ((hgAt t ht).differentiableAt two_ne_zero).differentiableWithinAt
  have hgDerivDiff : DifferentiableOn ℝ (deriv g) I := by
    intro t ht
    have hderivAt : DifferentiableAt ℝ (deriv g) t := by
      exact ((hgAt t ht).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact hderivAt.differentiableWithinAt
  have hgConv : ConvexOn ℝ I g := by
    -- The segment restriction is convex because its scalar second derivative is nonnegative.
    refine convexOn_of_deriv2_nonneg' (convex_Icc (0 : ℝ) 1) hgDiff hgDerivDiff ?_
    intro t ht
    rw [show (deriv^[2]) g t =
        (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] by
          simpa [g] using deriv2_lineMap_eq_iteratedFDeriv_diag hS_open hC2 hmem ht]
    exact hNonneg _ (hmem t ht) (y - x)
  have hdiffx : DifferentiableAt ℝ f x :=
    (hC2.contDiffAt (hS_open.mem_nhds hx)).differentiableAt two_ne_zero
  have hderiv_g :
      HasDerivAt g (inner ℝ (gradient f x) (y - x)) 0 := by
    -- The derivative at the left endpoint is the directional derivative in direction `y - x`.
    change HasDerivAt (f ∘ AffineMap.lineMap x y) (inner ℝ (gradient f x) (y - x)) 0
    simpa using
      (hdiffx.hasGradientAt.hasFDerivAt.comp_hasDerivAt_of_eq
        (hf := AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := 0))
        (hy := (AffineMap.lineMap_apply_zero x y).symm))
  have hslope :
      inner ℝ (gradient f x) (y - x) ≤ f y - f x := by
    -- Compare the left derivative to the secant slope of the convex scalar restriction.
    have h' := hgConv.deriv_le_slope (by simp [I]) (by simp [I]) zero_lt_one
      hderiv_g.differentiableAt
    rw [hderiv_g.deriv] at h'
    simpa [g, I, slope_def_field] using h'
  linarith

/-- Chapter01 Theorem 1.3.14 (1). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is twice continuously differentiable on `S`, then `f` is convex on `S` if and only
if the Hessian quadratic form, formalized by `iteratedFDeriv ℝ 2 f`, is nonnegative in every
direction at each point of `S`. -/
theorem convexOn_iff_iteratedFDeriv_nonneg
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S) :
    ConvexOn ℝ S f ↔
      ∀ x ∈ S, ∀ u : E, 0 ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
  constructor
  · intro hconv x hx u
    let φ : ℝ → E := AffineMap.lineMap x (x + u)
    have hφOpen : IsOpen (φ ⁻¹' S) := by
      -- The basepoint line stays inside `S` on a small symmetric interval because `S` is open.
      exact hS_open.preimage
        ((AffineMap.contDiff_lineMap x (x + u) : ContDiff ℝ 2 φ).continuous)
    have hφ0 : φ 0 ∈ S := by
      simpa [φ] using hx
    rcases Metric.isOpen_iff.mp hφOpen 0 hφ0 with ⟨δ, hδ, hball⟩
    let J : Set ℝ := Set.Icc (-(δ / 2)) (δ / 2)
    let g : ℝ → ℝ := fun t ↦ f (x + t • u)
    have hmem : ∀ t ∈ J, φ t ∈ S := by
      intro t ht
      have hle : |t| ≤ δ / 2 := by
        rw [abs_le]
        exact ht
      have hlt : |t| < δ := lt_of_le_of_lt hle (by linarith)
      have hdist : dist t 0 < δ := by simpa [Real.dist_eq] using hlt
      exact hball hdist
    have hLineConv : ConvexOn ℝ J g := by
      let T : Set ℝ := φ ⁻¹' S
      have hpre : ConvexOn ℝ T (f ∘ φ) := by
        simpa [T, φ] using hconv.comp_affineMap (AffineMap.lineMap x (x + u))
      have hpre' : ConvexOn ℝ T g := by
        refine hpre.congr ?_
        intro t ht
        simp [g, φ, AffineMap.lineMap_apply_module', add_comm]
      exact hpre'.subset hmem (convex_Icc _ _)
    have hgAt : ∀ t ∈ J, ContDiffAt ℝ 2 g t := by
      intro t ht
      have hfAt : ContDiffAt ℝ 2 f (φ t) := hC2.contDiffAt (hS_open.mem_nhds (hmem t ht))
      have hφAt : ContDiffAt ℝ 2 φ t := by
        simpa [φ] using (AffineMap.contDiff_lineMap x (x + u) : ContDiff ℝ 2 φ).contDiffAt
      have hEq : g = f ∘ φ := by
        funext s
        simp [g, φ, AffineMap.lineMap_apply_module', add_comm]
      rw [hEq]
      exact ContDiffAt.comp t hfAt hφAt
    have hgDiff : ∀ t ∈ J, DifferentiableAt ℝ g t := by
      intro t ht
      exact (hgAt t ht).differentiableAt two_ne_zero
    have hgDerivDiff0 : DifferentiableAt ℝ (deriv g) 0 := by
      have h0J : (0 : ℝ) ∈ J := by
        constructor <;> linarith [hδ]
      exact (((hgAt 0 h0J).derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    have hnonneg : 0 ≤ (deriv^[2]) g 0 := by
      -- Convexity of the scalar restriction forces a nonnegative second derivative at the basepoint.
      have hδhalf : 0 < δ / 2 := by positivity
      simpa [J] using
        deriv2_nonneg_at_zero_of_convexOn_interval hδhalf hLineConv hgDiff hgDerivDiff0
    have h0J : (0 : ℝ) ∈ J := by
      constructor <;> linarith [hδ]
    have hderiv2 :
        (deriv^[2]) g 0 = (iteratedFDeriv ℝ 2 f x) ![u, u] := by
      simpa [g, φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_module',
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (deriv2_lineMap_eq_iteratedFDeriv_diag hS_open hC2 hmem h0J)
    simpa [hderiv2] using hnonneg
  · intro hNonneg
    -- Package the segment-wise second-order estimate into the first-order support inequality.
    refine (convexOn_iff_ge_gradient_inner_sub hS_open hS_convex
      (hC2.differentiableOn two_ne_zero)).2 ?_
    intro x hx y hy
    exact ge_gradient_inner_sub_of_iteratedFDeriv_nonneg
      hS_open hS_convex hC2 hNonneg hx hy

/-- Chapter01 Theorem 1.3.14 (2). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is twice continuously differentiable on `S`, and if the Hessian quadratic form,
formalized by `iteratedFDeriv ℝ 2 f`, is positive in every nonzero direction at each point of
`S`, then `f` is strictly convex on `S`. -/
theorem strictConvexOn_of_iteratedFDeriv_pos
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S)
    (hPos :
      ∀ x ∈ S, ∀ u : E, u ≠ 0 → 0 < (iteratedFDeriv ℝ 2 f x) ![u, u]) :
    StrictConvexOn ℝ S f := by
  refine ⟨hS_convex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let I : Set ℝ := Set.Icc 0 1
  let g : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hmem : ∀ t ∈ I, AffineMap.lineMap x y t ∈ S := by
    intro t ht
    simpa [I] using hS_convex.lineMap_mem hx hy ht
  have hgAt : ∀ t ∈ I, ContDiffAt ℝ 2 g t := by
    intro t ht
    have hfAt : ContDiffAt ℝ 2 f (AffineMap.lineMap x y t) :=
      hC2.contDiffAt (hS_open.mem_nhds (hmem t ht))
    have hlineAt : ContDiffAt ℝ 2 (AffineMap.lineMap x y : ℝ → E) t := by
      simpa using
        (AffineMap.contDiff_lineMap x y : ContDiff ℝ 2 (AffineMap.lineMap x y : ℝ → E)).contDiffAt
    change ContDiffAt ℝ 2 (f ∘ AffineMap.lineMap x y) t
    exact ContDiffAt.comp t hfAt hlineAt
  have hgCont : ContinuousOn g I := by
    intro t ht
    exact (hgAt t ht).continuousAt.continuousWithinAt
  have hgStrict : StrictConvexOn ℝ I g := by
    -- The scalar restriction is strictly convex because its second derivative is positive.
    refine strictConvexOn_of_deriv2_pos' (convex_Icc (0 : ℝ) 1) hgCont ?_
    intro t ht
    rw [show (deriv^[2]) g t =
        (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)) ![y - x, y - x] by
          simpa [g] using deriv2_lineMap_eq_iteratedFDeriv_diag hS_open hC2 hmem ht]
    exact hPos _ (hmem t ht) (y - x) (sub_ne_zero.mpr hxy.symm)
  have hstrict_seg :
      g (a • (0 : ℝ) + b • (1 : ℝ)) < a • g 0 + b • g 1 := by
    -- Evaluate strict convexity on the endpoints of the unit interval.
    exact hgStrict.2 (by simp [I]) (by simp [I]) zero_ne_one ha hb hab
  have hba : 1 - b = a := by linarith
  -- The point `a • x + b • y` is the `b`-point on the segment from `x` to `y`.
  simpa [g, I, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_module, hab, hba, smul_eq_mul, add_comm, add_left_comm, add_assoc]
    using hstrict_seg

/-- Helper for Chapter01 Theorem 1.3.14: subtracting `(m / 2) * ‖z‖^2` preserves `C²` regularity
on the source domain. -/
lemma contDiffOn_sub_half_mul_norm_sq
    (hC2 : ContDiffOn ℝ 2 f S) (m : ℝ) :
    ContDiffOn ℝ 2 (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) S := by
  -- The shifted function keeps the source route: ordinary convexity of `f - (m / 2) * ‖·‖²`.
  have hquad : ContDiffOn ℝ 2 (fun z : E ↦ ‖z‖ ^ (2 : ℕ) * (m / 2 : ℝ)) S := by
    simpa using
      ((((contDiff_norm_sq ℝ :
          ContDiff ℝ 2 fun z : E ↦ ‖z‖ ^ (2 : ℕ)).smul_const (m / 2 : ℝ)).contDiffOn :
        ContDiffOn ℝ 2 (fun z : E ↦ ‖z‖ ^ (2 : ℕ) • (m / 2 : ℝ)) S))
  refine hC2.sub ?_
  simpa [mul_comm] using hquad

/-- Helper for Chapter01 Theorem 1.3.14: along the basepoint line `t ↦ x + t • u`, the quadratic
shift `(m / 2) * ‖·‖^2` has constant second derivative `m * ‖u‖^2`. -/
lemma deriv2_half_mul_norm_sq_line
    (m : ℝ) (x u : E) :
    (deriv^[2]) (fun t : ℝ ↦ (m / 2) * ‖x + t • u‖ ^ (2 : ℕ)) 0 =
      m * ‖u‖ ^ (2 : ℕ) := by
  let q : ℝ → ℝ := fun t ↦ (m / 2) * ‖x + t • u‖ ^ (2 : ℕ)
  have hray : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • u) u t := by
    intro t
    -- The restriction uses the affine line through `x` with direction `u`.
    simpa [one_smul] using ((hasDerivAt_id' t).smul_const u).const_add x
  have hnormSq : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ ‖x + s • u‖ ^ (2 : ℕ))
        (2 * inner ℝ (x + t • u) u) t := by
    intro t
    simpa using (hray t).norm_sq
  have hqDeriv : ∀ t : ℝ,
      HasDerivAt q ((m / 2) * (2 * inner ℝ (x + t • u) u)) t := by
    intro t
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using (hnormSq t).const_mul (m / 2 : ℝ)
  have hqDerivEq :
      deriv q = fun t : ℝ ↦ (m / 2) * (2 * inner ℝ (x + t • u) u) := by
    funext t
    exact (hqDeriv t).deriv
  have hinner : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ inner ℝ (x + s • u) u) (‖u‖ ^ (2 : ℕ)) t := by
    intro t
    -- Differentiating the inner product kills the constant term and leaves `inner u u`.
    simpa [real_inner_self_eq_norm_sq] using
      (hray t).inner ℝ (hasDerivAt_const t u)
  have hqSecond :
      HasDerivAt (deriv q) (((m / 2) * 2) * ‖u‖ ^ (2 : ℕ)) 0 := by
    rw [hqDerivEq]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hinner 0).const_mul ((m / 2) * 2 : ℝ)
  -- The first derivative is affine in `t`, so the second derivative is the constant Hessian term.
  simpa [q, Function.iterate_succ_apply] using hqSecond.deriv

/-- Helper for Chapter01 Theorem 1.3.14: the Hessian diagonal of the shifted function
`z ↦ f z - (m / 2) * ‖z‖^2` is the Hessian diagonal of `f` minus `m * ‖u‖^2`. -/
lemma iteratedFDeriv_diag_sub_half_mul_norm_sq
    (hS_open : IsOpen S) (hC2 : ContDiffOn ℝ 2 f S)
    {m : ℝ} {x : E} (hx : x ∈ S) (u : E) :
    (iteratedFDeriv ℝ 2 (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) x) ![u, u] =
      (iteratedFDeriv ℝ 2 f x) ![u, u] - m * ‖u‖ ^ (2 : ℕ) := by
  let φ : ℝ → E := AffineMap.lineMap x (x + u)
  let I : Set ℝ := {0}
  have h0I : (0 : ℝ) ∈ I := by simp [I]
  have hmem : ∀ t ∈ I, φ t ∈ S := by
    intro t ht
    have ht0 : t = 0 := by simpa [I] using ht
    simpa [φ, ht0] using hx
  have hfLine :
      (deriv^[2]) (fun s : ℝ ↦ f (φ s)) 0 =
        (iteratedFDeriv ℝ 2 f x) ![u, u] := by
    -- Evaluate the Hessian of `f` through the basepoint line `x + s • u`.
    simpa [φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_module',
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      deriv2_lineMap_eq_iteratedFDeriv_diag hS_open hC2 hmem h0I
  have hgLine :
      (deriv^[2]) (fun s : ℝ ↦
        (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) (φ s)) 0 =
          (iteratedFDeriv ℝ 2 (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) x) ![u, u] := by
    -- Apply the same line-restriction bridge to the shifted function.
    simpa [φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_module',
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      deriv2_lineMap_eq_iteratedFDeriv_diag hS_open
        (contDiffOn_sub_half_mul_norm_sq (f := f) (S := S) hC2 m) hmem h0I
  have hfAt : ContDiffAt ℝ 2 f x := hC2.contDiffAt (hS_open.mem_nhds hx)
  have hφAt : ContDiffAt ℝ 2 φ 0 := by
    simpa [φ] using
      (AffineMap.contDiff_lineMap x (x + u) : ContDiff ℝ 2 φ).contDiffAt
  have hLinefAt : ContDiffAt ℝ 2 (fun s : ℝ ↦ f (φ s)) 0 := by
    -- The source `C²` regularity transfers to the scalar line restriction.
    have hfAt0 : ContDiffAt ℝ 2 f (φ 0) := by simpa [φ] using hfAt
    change ContDiffAt ℝ 2 (f ∘ φ) 0
    exact ContDiffAt.comp 0 hfAt0 hφAt
  have hLineqAt : ContDiffAt ℝ 2 (fun s : ℝ ↦ (m / 2) * ‖x + s • u‖ ^ (2 : ℕ)) 0 := by
    -- The quadratic correction is the smooth norm-square composed with the same affine line.
    have hNormSqLineAt : ContDiffAt ℝ 2 (fun s : ℝ ↦ ‖φ s‖ ^ (2 : ℕ)) 0 := by
      exact (contDiff_norm_sq ℝ).contDiffAt.comp 0 hφAt
    have hScaled :
        ContDiffAt ℝ 2 (fun s : ℝ ↦ ‖φ s‖ ^ (2 : ℕ) • (m / 2 : ℝ)) 0 :=
      hNormSqLineAt.smul_const (m / 2 : ℝ)
    simpa [φ, smul_eq_mul, mul_comm, AffineMap.lineMap_apply_module', sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using hScaled
  have hsub :
      (deriv^[2]) (fun s : ℝ ↦
        (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) (φ s)) 0 =
          (deriv^[2]) (fun s : ℝ ↦ f (φ s)) 0 - m * ‖u‖ ^ (2 : ℕ) := by
    have hcomp :
        (fun s : ℝ ↦ (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) (φ s)) =
          (fun s : ℝ ↦ f (φ s)) - fun s : ℝ ↦ (m / 2) * ‖x + s • u‖ ^ (2 : ℕ) := by
      funext s
      simp [φ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hcomp]
    rw [← iteratedDeriv_eq_iterate]
    calc
      iteratedDeriv 2
          ((fun s : ℝ ↦ f (φ s)) - fun s : ℝ ↦ (m / 2) * ‖x + s • u‖ ^ (2 : ℕ)) 0
          = iteratedDeriv 2 (fun s : ℝ ↦ f (φ s)) 0
              - iteratedDeriv 2 (fun s : ℝ ↦ (m / 2) * ‖x + s • u‖ ^ (2 : ℕ)) 0 := by
              simpa using iteratedDeriv_sub hLinefAt hLineqAt
      _ = (deriv^[2]) (fun s : ℝ ↦ f (φ s)) 0
            - (deriv^[2]) (fun s : ℝ ↦ (m / 2) * ‖x + s • u‖ ^ (2 : ℕ)) 0 := by
              rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
      _ = (deriv^[2]) (fun s : ℝ ↦ f (φ s)) 0 - m * ‖u‖ ^ (2 : ℕ) := by
              rw [deriv2_half_mul_norm_sq_line m x u]
  -- Rewrite the shifted Hessian by comparing second derivatives along the same affine line.
  calc
    (iteratedFDeriv ℝ 2 (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) x) ![u, u]
        = (deriv^[2]) (fun s : ℝ ↦
            (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) (φ s)) 0 := by
              symm
              exact hgLine
    _ = (deriv^[2]) (fun s : ℝ ↦ f (φ s)) 0 - m * ‖u‖ ^ (2 : ℕ) := hsub
    _ = (iteratedFDeriv ℝ 2 f x) ![u, u] - m * ‖u‖ ^ (2 : ℕ) := by
          rw [hfLine]

/-- Helper for Chapter01 Theorem 1.3.14: fixed-parameter strong convexity is equivalent to a
uniform Hessian lower bound after shifting by `(m / 2) * ‖·‖^2`. -/
lemma strongConvexOn_iff_iteratedFDeriv_lower_bound
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S)
    (m : ℝ) :
    StrongConvexOn S m f ↔
      ∀ x ∈ S, ∀ u : E, m * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
  let gfun : E → ℝ := fun z ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)
  have hgC2 : ContDiffOn ℝ 2 gfun S := by
    simpa [gfun] using contDiffOn_sub_half_mul_norm_sq (f := f) (S := S) hC2 m
  have hshift :
      StrongConvexOn S m f ↔ ConvexOn ℝ S gfun := by
    -- Route correction: part (3) should follow the source's shifted-function architecture,
    -- not the earlier shifted-segment packaging.
    simpa [gfun] using (strongConvexOn_iff_convex (s := S) (m := m) (f := f))
  have hhess :
      (∀ x ∈ S, ∀ u : E, 0 ≤ (iteratedFDeriv ℝ 2 gfun x) ![u, u]) ↔
        ∀ x ∈ S, ∀ u : E, m * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
    constructor
    · intro h x hx u
      have hx' := h x hx u
      rw [show (iteratedFDeriv ℝ 2 gfun x) ![u, u] =
          (iteratedFDeriv ℝ 2 f x) ![u, u] - m * ‖u‖ ^ (2 : ℕ) by
            simpa [gfun] using
              iteratedFDeriv_diag_sub_half_mul_norm_sq hS_open hC2 hx u] at hx'
      linarith
    · intro h x hx u
      have hx' := h x hx u
      rw [show (iteratedFDeriv ℝ 2 gfun x) ![u, u] =
          (iteratedFDeriv ℝ 2 f x) ![u, u] - m * ‖u‖ ^ (2 : ℕ) by
            simpa [gfun] using
              iteratedFDeriv_diag_sub_half_mul_norm_sq hS_open hC2 hx u]
      linarith
  -- Apply the part-(1) Hessian criterion to the shifted function.
  exact hshift.trans ((convexOn_iff_iteratedFDeriv_nonneg hS_open hS_convex hgC2).trans hhess)

/-- Chapter01 Theorem 1.3.14 (3). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is twice continuously differentiable on `S`, then `f` is uniformly convex on `S`,
formalized as `∃ m > 0, StrongConvexOn S m f`, if and only if its Hessian quadratic form is
uniformly positive definite on `S`, i.e. there exists `m > 0` such that
`m * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u]` for all `x ∈ S` and `u : E`. -/
theorem exists_strongConvexOn_iff_iteratedFDeriv_uniformly_pos
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hC2 : ContDiffOn ℝ 2 f S) :
    (∃ m > 0, StrongConvexOn S m f) ↔
      ∃ m > 0, ∀ x ∈ S, ∀ u : E,
        m * ‖u‖ ^ (2 : ℕ) ≤ (iteratedFDeriv ℝ 2 f x) ![u, u] := by
  constructor
  · rintro ⟨m, hm, hstrong⟩
    -- Route correction: package part (3) through the shifted function
    -- `z ↦ f z - (m / 2) * ‖z‖^2`, then invoke the already-proved part (1).
    refine ⟨m, hm, ?_⟩
    exact (strongConvexOn_iff_iteratedFDeriv_lower_bound hS_open hS_convex hC2 m).1 hstrong
  · rintro ⟨m, hm, hbound⟩
    -- The same fixed-parameter equivalence converts the Hessian lower bound back to
    -- strong convexity without introducing any new segment-support API.
    refine ⟨m, hm, ?_⟩
    exact (strongConvexOn_iff_iteratedFDeriv_lower_bound hS_open hS_convex hC2 m).2 hbound

end Theorem1314
