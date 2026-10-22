/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Lemma 5.1.2: at a fixed point of the open domain, the source-facing diagonal bound
rewrites directly as the corresponding diagonal estimate for `iteratedFDeriv ℝ 3 f x`. -/
private theorem iteratedFDeriv_diagonal_bound_at_point
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hdiag : ∀ {x : E} (hx : x ∈ dom) (u : E),
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ))
    {x : E} (hx : x ∈ dom) :
    ∀ u : E,
      |iteratedFDeriv ℝ 3 f x ![u, u, u]| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
  intro u
  -- Move from the textbook third directional derivative to the canonical iterated derivative.
  have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
  have hconst : (fun _ : Fin 3 => u) = ![u, u, u] := by
    ext i
    fin_cases i <;> rfl
  have hdiag' :
      |iteratedFDeriv ℝ 3 f x (fun _ ↦ u)| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt] using hdiag hx u
  simpa [hconst] using hdiag'

/-- Helper for Lemma 5.1.2: under `C³` regularity, the third iterated derivative is symmetric in
its first two arguments. -/
private theorem iteratedFDeriv_three_swap12
    {f : E → ℝ} {x u₁ u₂ u₃ : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f x ![u₂, u₁, u₃] := by
  -- View the third derivative as the second derivative of `fderiv ℝ f`, then apply the standard
  -- symmetry theorem for second derivatives.
  let g : E → E →L[ℝ] ℝ := fderiv ℝ f
  have hgcont : ContDiffAt ℝ 2 g x := by
    simpa [g] using hcontAt.fderiv_right (m := 2) (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgsymm : IsSymmSndFDerivAt ℝ g x := hgcont.isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ g) x u₁ u₂) u₃ =
        (fderiv ℝ (fderiv ℝ g) x u₂ u₁) u₃ := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L u₃) (hgsymm.eq u₁ u₂)
  simpa [g, iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply] using hswap

/-- Helper for Lemma 5.1.2: on an open `C³` domain, the third iterated derivative is symmetric in
its last two arguments as well. -/
private theorem iteratedFDeriv_three_swap23
    {dom : Set E} {f : E → ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E) :
    iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f x ![u₁, u₃, u₂] := by
  let c : E → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ := iteratedFDeriv ℝ 2 f
  -- The second derivative is symmetric at nearby points, so the antisymmetric part vanishes on a
  -- neighborhood of `x`, and therefore so does its derivative at `x`.
  have hvanish :
      (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hdom_open.mem_nhds hx] with y hy
    have hycont : ContDiffAt ℝ 2 f y := by
      exact (hcont.of_le (by norm_num)).contDiffAt (hdom_open.mem_nhds hy)
    have hysymm : IsSymmSndFDerivAt ℝ f y := hycont.isSymmSndFDerivAt (by norm_num)
    have hyEq : iteratedFDeriv ℝ 2 f y ![u₂, u₃] = iteratedFDeriv ℝ 2 f y ![u₃, u₂] :=
      hysymm.iteratedFDeriv_cons
    simpa [c, hyEq]
  have hc_diff : DifferentiableAt ℝ c x := by
    have hc_contDiff : ContDiffAt ℝ 1 c x := by
      exact
        (hcont.contDiffAt (hdom_open.mem_nhds hx)).iteratedFDeriv_right
          (m := 1) (i := 2) (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
    exact hc_contDiff.differentiableAt one_ne_zero
  have hderivZero :
      fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) x = 0 := by
    -- Replace the function by the eventually equal constant zero function.
    rw [hvanish.fderiv_eq]
    simp
  have hderivEval :
      ((fderiv ℝ c x).flipMultilinear ![u₂, u₃]) u₁ =
        ((fderiv ℝ c x).flipMultilinear ![u₃, u₂]) u₁ := by
    have hzeroApplied :
        (fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) x) u₁ = 0 := by
      simpa using congrArg (fun L : E →L[ℝ] ℝ => L u₁) hderivZero
    have h23diff : DifferentiableAt ℝ (fun y ↦ c y ![u₂, u₃]) x :=
      hc_diff.continuousMultilinear_apply_const ![u₂, u₃]
    have h32diff : DifferentiableAt ℝ (fun y ↦ c y ![u₃, u₂]) x :=
      hc_diff.continuousMultilinear_apply_const ![u₃, u₂]
    have hzeroApplied' :
        (((fderiv ℝ c x).flipMultilinear ![u₂, u₃] -
            (fderiv ℝ c x).flipMultilinear ![u₃, u₂]) u₁) = 0 := by
      rw [← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_sub h23diff h32diff]
      exact hzeroApplied
    exact sub_eq_zero.mp hzeroApplied'
  simpa [c, iteratedFDeriv_succ_apply_left] using hderivEval

/-- Helper for Lemma 5.1.2: when the Hessian quadratic form is nonnegative, the square of the
local norm rewrites back to that quadratic form. -/
private lemma sq_hessianLocalNorm_eq_inner_of_nonneg
    {f : E → ℝ} {x u : E} (hquad : 0 ≤ inner ℝ u (hessian f x u)) :
    ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Lemma 5.1.2: the Hessian bilinear form at `x`, written in the operator-first
convention used by the local-radical API. -/
private def hessianBilinAt (f : E → ℝ) (x : E) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (hessian f x)).toBilinForm

/-- Helper for Lemma 5.1.2: evaluating `hessianBilinAt` pairs the Hessian image of the first
argument with the second argument. -/
private lemma hessianBilinAt_apply (f : E → ℝ) (x u v : E) :
    hessianBilinAt f x u v = inner ℝ (hessian f x u) v :=
  rfl

/-- Helper for Lemma 5.1.2: a zero Hessian local norm is equivalent to vanishing under the
Hessian operator itself. -/
private lemma hessian_localRadical_iff_hessian_eq_zero
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) :
    ‖u‖[f; x] = 0 ↔ hessian f x u = 0 := by
  let B : LinearMap.BilinForm ℝ E := hessianBilinAt f x
  have hB_nonneg : ∀ a : E, 0 ≤ (B a) a := by
    intro a
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hxPos.inner_nonneg_right a
  have hB_symm : LinearMap.IsSymm B := by
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro a b
    change inner ℝ (hessian f x a) b = inner ℝ (hessian f x b) a
    simpa [real_inner_comm] using hxPos.isSymmetric a b
  constructor
  · intro hu
    have hu_quad_nonneg : 0 ≤ inner ℝ u (hessian f x u) := hxPos.inner_nonneg_right u
    have hu_sq :
        ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) :=
      sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u) hu_quad_nonneg
    have hu_quad : (B u) u = 0 := by
      have hu_sq_zero : ‖u‖[f; x] ^ (2 : ℕ) = 0 := by simpa [hu]
      have hu_inner_zero : inner ℝ u (hessian f x u) = 0 := by
        nlinarith [hu_sq, hu_sq_zero]
      simpa [B, hessianBilinAt_apply, real_inner_comm] using hu_inner_zero
    have hu_ker : u ∈ LinearMap.ker B :=
      (LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hB_nonneg hB_symm).1 hu_quad
    have hu_ker' : B u = 0 := by
      simpa [LinearMap.mem_ker] using hu_ker
    have hself_zero : inner ℝ (hessian f x u) (hessian f x u) = 0 := by
      simpa [B, hessianBilinAt_apply] using
        congrArg (fun L : E →ₗ[ℝ] ℝ => L (hessian f x u)) hu_ker'
    exact inner_self_eq_zero.mp hself_zero
  · intro hu
    have hu_sq :
        ‖u‖[f; x] ^ (2 : ℕ) = 0 := by
      rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u)
        (hxPos.inner_nonneg_right u)]
      simp [hu]
    have hu_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
    nlinarith

/-- Helper for Lemma 5.1.2: a zero Hessian local norm is equivalent to annihilating every
Hessian bilinear pairing at the base point. -/
private lemma hessian_localRadical_iff_annihilates_hessian
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) :
    ‖u‖[f; x] = 0 ↔ ∀ z : E, inner ℝ u (hessian f x z) = 0 := by
  constructor
  · intro hu z
    have hHu : hessian f x u = 0 :=
      (hessian_localRadical_iff_hessian_eq_zero (f := f) (x := x) (u := u) hxPos).1 hu
    have hsym : inner ℝ (hessian f x u) z = inner ℝ u (hessian f x z) := by
      simpa [real_inner_comm] using hxPos.isSymmetric u z
    simpa [hHu] using hsym.symm
  · intro hu
    have huu : inner ℝ u (hessian f x u) = 0 := hu u
    have hu_sq :
        ‖u‖[f; x] ^ (2 : ℕ) = 0 := by
      rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u)
        (hxPos.inner_nonneg_right u)]
      simpa [huu]
    have hu_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
    nlinarith

/-- Helper for Lemma 5.1.2: adding a Hessian-radical direction only rescales the local norm by
the scalar on the transverse direction. -/
private lemma hessianLocalNorm_add_smul_of_localRadical
    {f : E → ℝ} {x u w : E} (hxPos : (hessian f x).IsPositive)
    (hu : ∀ z : E, inner ℝ u (hessian f x z) = 0) (t : ℝ) :
    ‖u + t • w‖[f; x] = |t| * ‖w‖[f; x] := by
  have hHu : hessian f x u = 0 :=
    (hessian_localRadical_iff_hessian_eq_zero (f := f) (x := x) (u := u) hxPos).1
      ((hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u) hxPos).2 hu)
  have hquad :
      inner ℝ (u + t • w) (hessian f x (u + t • w)) =
        t ^ (2 : ℕ) * inner ℝ w (hessian f x w) := by
    calc
      inner ℝ (u + t • w) (hessian f x (u + t • w))
          = inner ℝ (u + t • w) (t • hessian f x w) := by simp [hHu, map_add]
      _ = inner ℝ u (t • hessian f x w) + inner ℝ (t • w) (t • hessian f x w) := by
            rw [inner_add_left]
      _ = t * inner ℝ u (hessian f x w) + t * (t * inner ℝ w (hessian f x w)) := by
            simp [inner_smul_left, inner_smul_right, mul_assoc]
      _ = t ^ (2 : ℕ) * inner ℝ w (hessian f x w) := by
            simp [hu w, pow_two, mul_assoc]
  have hw_quad_nonneg : 0 ≤ inner ℝ w (hessian f x w) := hxPos.inner_nonneg_right w
  -- Expand both local norms and use the exact quadratic identity coming from the radical
  -- annihilation of the mixed terms.
  rw [hessianLocalNorm_def, hquad, hessianLocalNorm_def]
  rw [Real.sqrt_mul (sq_nonneg t)]
  simp [Real.sqrt_sq_eq_abs]

/-- Helper for Lemma 5.1.2: decompose a direction into its Hessian-orthogonal projection onto the
span of `v` and the corresponding residual. -/
private lemma hessianProjectionSplit
    {f : E → ℝ} {x d v : E} (hxPos : (hessian f x).IsPositive)
    (hv : ‖v‖[f; x] ≠ 0) :
    let α : ℝ := inner ℝ d (hessian f x v) / ‖v‖[f; x] ^ (2 : ℕ)
    let w : E := d - α • v
    inner ℝ w (hessian f x v) = 0 ∧
      ‖d‖[f; x] ^ (2 : ℕ) = ‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
  let α : ℝ := inner ℝ d (hessian f x v) / ‖v‖[f; x] ^ (2 : ℕ)
  let w : E := d - α • v
  have hv_sq_nonneg : 0 ≤ inner ℝ v (hessian f x v) := hxPos.inner_nonneg_right v
  have hv_sq :
      ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ v (hessian f x v) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := v) hv_sq_nonneg
  have hv_sq_ne : ‖v‖[f; x] ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 hv
  have hα :
      α * ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ d (hessian f x v) := by
    dsimp [α]
    field_simp [hv_sq_ne]
  have horth :
      inner ℝ w (hessian f x v) = 0 := by
    -- The projection coefficient is chosen to cancel the mixed Hessian pairing with `v`.
    calc
      inner ℝ w (hessian f x v)
          = inner ℝ d (hessian f x v) - α * inner ℝ v (hessian f x v) := by
              simp [w, inner_sub_left, inner_smul_left]
      _ = inner ℝ d (hessian f x v) - α * ‖v‖[f; x] ^ (2 : ℕ) := by
            rw [hv_sq]
      _ = 0 := by nlinarith [hα]
  have horth' :
      inner ℝ v (hessian f x w) = 0 := by
    -- Symmetry of the positive Hessian operator moves the orthogonality to the other slot.
    have hsym : inner ℝ v (hessian f x w) = inner ℝ w (hessian f x v) := by
      simpa [real_inner_comm] using (hxPos.isSymmetric v w).symm
    simpa [horth] using hsym
  have hw_sq_nonneg : 0 ≤ inner ℝ w (hessian f x w) := hxPos.inner_nonneg_right w
  have hw_sq :
      ‖w‖[f; x] ^ (2 : ℕ) = inner ℝ w (hessian f x w) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := w) hw_sq_nonneg
  have hd_sq_nonneg : 0 ≤ inner ℝ d (hessian f x d) := hxPos.inner_nonneg_right d
  have hd_sq :
      ‖d‖[f; x] ^ (2 : ℕ) = inner ℝ d (hessian f x d) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := d) hd_sq_nonneg
  have hd_eq : d = w + α • v := by
    -- Rewrite `d` back as the residual plus its Hessian projection onto `v`.
    dsimp [w]
    abel_nf
  have hpyth_inner :
      inner ℝ d (hessian f x d) =
        inner ℝ w (hessian f x w) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
    -- Expand the Hessian quadratic form of the decomposition and cancel the mixed terms.
    calc
      inner ℝ d (hessian f x d)
          = inner ℝ (w + α • v) (hessian f x (w + α • v)) := by rw [hd_eq]
      _ = inner ℝ (w + α • v) (hessian f x w + α • hessian f x v) := by
            simp [map_add]
      _ = inner ℝ w (hessian f x w) + α * inner ℝ w (hessian f x v) +
            α * inner ℝ v (hessian f x w) + α * (α * inner ℝ v (hessian f x v)) := by
              simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
              ring
      _ = inner ℝ w (hessian f x w) + α * (α * inner ℝ v (hessian f x v)) := by
            simp [horth, horth']
      _ = inner ℝ w (hessian f x w) + α ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) := by
            rw [hv_sq]
            ring
      _ = inner ℝ w (hessian f x w) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by ring
  constructor
  · exact horth
  · rw [hd_sq, hw_sq]
    exact hpyth_inner

/-- Helper for Lemma 5.1.2: a Hessian-local orthonormal pair models the local norm by the
Euclidean norm of the scalar coefficients. -/
private lemma hessianLocalNorm_sq_of_localOrthonormalPair
    {f : E → ℝ} {x e₁ e₂ : E} (hxPos : (hessian f x).IsPositive)
    (he₁ : ‖e₁‖[f; x] = 1) (he₂ : ‖e₂‖[f; x] = 1)
    (horth : inner ℝ e₁ (hessian f x e₂) = 0) :
    ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  have he₁_sq_nonneg : 0 ≤ inner ℝ e₁ (hessian f x e₁) := hxPos.inner_nonneg_right e₁
  have he₂_sq_nonneg : 0 ≤ inner ℝ e₂ (hessian f x e₂) := hxPos.inner_nonneg_right e₂
  have he₁_sq : inner ℝ e₁ (hessian f x e₁) = 1 := by
    simpa [he₁] using
      (sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (x := x) (u := e₁) he₁_sq_nonneg).symm
  have he₂_sq : inner ℝ e₂ (hessian f x e₂) = 1 := by
    simpa [he₂] using
      (sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (x := x) (u := e₂) he₂_sq_nonneg).symm
  have horth' : inner ℝ e₂ (hessian f x e₁) = 0 := by
    -- Symmetry moves the orthogonality relation to the opposite Hessian slot.
    have hsym : inner ℝ e₂ (hessian f x e₁) = inner ℝ e₁ (hessian f x e₂) := by
      simpa [real_inner_comm] using (hxPos.isSymmetric e₂ e₁).symm
    simpa [horth] using hsym
  intro a b
  have hab_nonneg : 0 ≤ inner ℝ (a • e₁ + b • e₂) (hessian f x (a • e₁ + b • e₂)) :=
    hxPos.inner_nonneg_right (a • e₁ + b • e₂)
  -- Expand the Hessian quadratic form in the local-orthonormal basis and cancel the cross terms.
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := a • e₁ + b • e₂) hab_nonneg]
  simp [map_add, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, horth,
    horth', he₁_sq, he₂_sq, pow_two]

/-- Helper for Lemma 5.1.2: a trilinear map is additive in its first slot. -/
private lemma trilinearApplyAddFirst
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a₁ a₂ b c : E) :
    T ![a₁ + a₂, b, c] = T ![a₁, b, c] + T ![a₂, b, c] := by
  -- Rewrite the first-slot addition through the `Fin 3` `cons` API.
  simpa using T.cons_add ![b, c] a₁ a₂

/-- Helper for Lemma 5.1.2: a trilinear map is additive in its second slot. -/
private lemma trilinearApplyAddSecond
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a b₁ b₂ c : E) :
    T ![a, b₁ + b₂, c] = T ![a, b₁, c] + T ![a, b₂, c] := by
  -- Curry once so that the second slot becomes the first slot of a bilinear map.
  simpa using (T.curryLeft a).cons_add ![c] b₁ b₂

/-- Helper for Lemma 5.1.2: a trilinear map is additive in its third slot. -/
private lemma trilinearApplyAddThird
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a b c₁ c₂ : E) :
    T ![a, b, c₁ + c₂] = T ![a, b, c₁] + T ![a, b, c₂] := by
  -- Curry on the right so the last slot becomes an ordinary linear map.
  simpa using (T.curryRight ![a, b]).map_add c₁ c₂

/-- Helper for Lemma 5.1.2: a trilinear map is homogeneous in its first slot. -/
private lemma trilinearApplySmulFirst
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![t • a, b, c] = t * T ![a, b, c] := by
  -- Rewrite the first-slot scaling through the `Fin 3` `cons` API.
  simpa [smul_eq_mul] using T.cons_smul ![b, c] t a

/-- Helper for Lemma 5.1.2: a trilinear map is homogeneous in its second slot. -/
private lemma trilinearApplySmulSecond
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![a, t • b, c] = t * T ![a, b, c] := by
  -- Curry once so that the second slot becomes the first slot of a bilinear map.
  simpa [smul_eq_mul] using (T.curryLeft a).cons_smul ![c] t b

/-- Helper for Lemma 5.1.2: a trilinear map is homogeneous in its third slot. -/
private lemma trilinearApplySmulThird
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![a, b, t • c] = t * T ![a, b, c] := by
  have hvec : Function.update ![a, b, c] 2 (t • c) = ![a, b, t • c] := by
    -- Normalize the third-slot update to the vector literal used throughout the file.
    ext i
    fin_cases i <;> rfl
  have hself : Function.update ![a, b, c] 2 c = ![a, b, c] := by
    -- The untouched third slot rewrites back to the original vector literal.
    ext i
    fin_cases i <;> rfl
  rw [← hvec, T.map_update_smul, hself]
  simp [smul_eq_mul]

/-- Helper for Lemma 5.1.2: the centered second difference of a symmetric trilinear form isolates
its `(u,w,w)` coefficient. -/
private lemma symmetricTrilinear_centeredSecondDifference
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (u w : E) (t : ℝ) :
    T ![u + t • w, u + t • w, u + t • w] +
        T ![u - t • w, u - t • w, u - t • w] -
          2 * T ![u, u, u] =
      6 * t ^ (2 : ℕ) * T ![u, w, w] := by
  have hplus :
      T ![u + t • w, u + t • w, u + t • w]
        = T ![u, u, u] + t * T ![u, u, w] + t * T ![u, w, u] + t * (t * T ![u, w, w]) +
            (t * T ![w, u, u] + t * (t * T ![w, u, w]) + t * (t * T ![w, w, u]) +
              t * (t * (t * T ![w, w, w]))) := by
    -- Expand the three `u + t • w` slots one at a time so every monomial appears explicitly.
    rw [trilinearApplyAddFirst]
    rw [trilinearApplyAddSecond, trilinearApplyAddSecond]
    rw [trilinearApplyAddThird, trilinearApplyAddThird, trilinearApplyAddThird,
      trilinearApplyAddThird]
    rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
      trilinearApplySmulThird]
    rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
      trilinearApplySmulSecond, trilinearApplySmulFirst, trilinearApplySmulFirst,
      trilinearApplySmulFirst, trilinearApplySmulFirst]
    ring
  have hminus :
      T ![u - t • w, u - t • w, u - t • w]
        = T ![u, u, u] + (-t) * T ![u, u, w] + (-t) * T ![u, w, u] +
            (-t) * ((-t) * T ![u, w, w]) +
            ((-t) * T ![w, u, u] + (-t) * ((-t) * T ![w, u, w]) +
              (-t) * ((-t) * T ![w, w, u]) + (-t) * ((-t) * ((-t) * T ![w, w, w]))) := by
    -- Rewrite `u - t • w` as `u + (-t) • w` and repeat the same slotwise expansion.
    rw [show u - t • w = u + (-t) • w by simp [sub_eq_add_neg]]
    rw [trilinearApplyAddFirst]
    rw [trilinearApplyAddSecond, trilinearApplyAddSecond]
    rw [trilinearApplyAddThird, trilinearApplyAddThird, trilinearApplyAddThird,
      trilinearApplyAddThird]
    rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
      trilinearApplySmulThird]
    rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
      trilinearApplySmulSecond, trilinearApplySmulFirst, trilinearApplySmulFirst,
      trilinearApplySmulFirst, trilinearApplySmulFirst]
    ring
  rw [hplus, hminus]
  -- Collapse the three two-`w` monomials to the common symmetric representative `T[u,w,w]`.
  rw [hswap23 u w u, hswap12 w u u, hswap23 u w u, hswap12 w u w, hswap23 w w u,
    hswap12 w u w]
  ring

/-- Helper for Lemma 5.1.2: the third iterated derivative vanishes in the `(u,w,w)` slot
pattern when `u` lies in the Hessian local radical. -/
private lemma iteratedFDeriv_vanishes_on_hessian_localRadical
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u w : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hx : x ∈ dom)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_iter : ∀ z : E,
      |iteratedFDeriv ℝ 3 f x ![z, z, z]| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    (hu : ∀ z : E, inner ℝ u (hessian f x z) = 0) :
    iteratedFDeriv ℝ 3 f x ![u, w, w] = 0 := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
  have huNorm : ‖u‖[f; x] = 0 :=
    (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u) hxPos).2 hu
  have huuu : T ![u, u, u] = 0 := by
    have hdiag_u : |T ![u, u, u]| ≤ 0 := by
      -- The diagonal cubic bound collapses to zero because `u` has zero Hessian local norm.
      simpa [T, huNorm] using hdiag_iter u
    exact abs_eq_zero.mp (le_antisymm hdiag_u (abs_nonneg _))
  have hswap12 :
      ∀ a b c : E, T ![a, b, c] = T ![b, a, c] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap12
        (f := f) (x := x) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hswap23 :
      ∀ a b c : E, T ![a, b, c] = T ![a, c, b] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap23
        (dom := dom) (f := f) hdom_open hcont hx a b c
  have hplusDiag (t : ℝ) :
      |T ![u + t • w, u + t • w, u + t • w]| ≤
        2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
    have hnorm :
        ‖u + t • w‖[f; x] = |t| * ‖w‖[f; x] :=
      hessianLocalNorm_add_smul_of_localRadical
        (f := f) (x := x) (u := u) (w := w) hxPos hu t
    -- Rewrite the diagonal bound on the translated direction through the radical norm collapse.
    simpa [T, hnorm] using hdiag_iter (u + t • w)
  have hminusDiag (t : ℝ) :
      |T ![u - t • w, u - t • w, u - t • w]| ≤
        2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
    have hnorm :
        ‖u - t • w‖[f; x] = |t| * ‖w‖[f; x] := by
      calc
        ‖u - t • w‖[f; x] = ‖u + (-t) • w‖[f; x] := by simp [sub_eq_add_neg]
        _ = |-t| * ‖w‖[f; x] :=
          hessianLocalNorm_add_smul_of_localRadical
            (f := f) (x := x) (u := u) (w := w) hxPos hu (-t)
        _ = |t| * ‖w‖[f; x] := by simp
    -- The same local-radical norm collapse applies to the reflected direction `u - t • w`.
    simpa [T, hnorm] using hdiag_iter (u - t • w)
  have hcoeffBound (t : ℝ) :
      |6 * t ^ (2 : ℕ) * T ![u, w, w]| ≤
        4 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
    have hcenter :
        T ![u + t • w, u + t • w, u + t • w] +
            T ![u - t • w, u - t • w, u - t • w] =
          6 * t ^ (2 : ℕ) * T ![u, w, w] := by
      simpa [huuu] using
        symmetricTrilinear_centeredSecondDifference T hswap12 hswap23 u w t
    rw [← hcenter]
    calc
      |T ![u + t • w, u + t • w, u + t • w] +
          T ![u - t • w, u - t • w, u - t • w]|
          ≤ |T ![u + t • w, u + t • w, u + t • w]| +
              |T ![u - t • w, u - t • w, u - t • w]| := abs_add_le _ _
      _ ≤ 2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) +
            2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
          gcongr
          · exact hplusDiag t
          · exact hminusDiag t
      _ = 4 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by ring
  have hsmall (t : ℝ) (ht : 0 < t) :
      |T ![u, w, w]| ≤ ((2 * (Mf : ℝ) * ‖w‖[f; x] ^ (3 : ℕ)) / 3) * t := by
    have hcoeff := hcoeffBound t
    have hcoeff' :
        6 * t ^ (2 : ℕ) * |T ![u, w, w]| ≤
          4 * (Mf : ℝ) * t ^ (3 : ℕ) * ‖w‖[f; x] ^ (3 : ℕ) := by
      have hleft :
          |6 * t ^ (2 : ℕ) * T ![u, w, w]| =
            6 * t ^ (2 : ℕ) * |T ![u, w, w]| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (6 : ℝ) by norm_num),
          abs_of_nonneg (pow_two_nonneg t)]
      have hright :
          4 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) =
            4 * (Mf : ℝ) * t ^ (3 : ℕ) * ‖w‖[f; x] ^ (3 : ℕ) := by
        rw [abs_of_pos ht]
        ring
      rwa [hleft, hright] at hcoeff
    have ht_sq_pos : 0 < t ^ (2 : ℕ) := by positivity
    have hfactored :
        t ^ (2 : ℕ) * (6 * |T ![u, w, w]|) ≤
          t ^ (2 : ℕ) * (4 * (Mf : ℝ) * t * ‖w‖[f; x] ^ (3 : ℕ)) := by
      nlinarith [hcoeff']
    have hlinear :
        6 * |T ![u, w, w]| ≤ 4 * (Mf : ℝ) * t * ‖w‖[f; x] ^ (3 : ℕ) := by
      nlinarith [hfactored, ht_sq_pos]
    nlinarith
  by_cases hzero : T ![u, w, w] = 0
  · simpa [T] using hzero
  have habs_pos : 0 < |T ![u, w, w]| := abs_pos.mpr hzero
  let K : ℝ := ((2 * (Mf : ℝ) * ‖w‖[f; x] ^ (3 : ℕ)) / 3)
  have hK_nonneg : 0 ≤ K := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by exact_mod_cast Mf.2
    have hw_nonneg : 0 ≤ ‖w‖[f; x] := hessianLocalNorm_nonneg f x w
    have hw_pow_nonneg : 0 ≤ ‖w‖[f; x] ^ (3 : ℕ) := pow_nonneg hw_nonneg _
    dsimp [K]
    nlinarith
  have hK_pos : 0 < K + 1 := by
    nlinarith
  let t0 : ℝ := |T ![u, w, w]| / (K + 1)
  have ht0_pos : 0 < t0 := by
    -- Choose an explicit positive step where the linear bound forces a contradiction.
    dsimp [t0]
    exact div_pos habs_pos hK_pos
  have hbound0 := hsmall t0 ht0_pos
  have hbound0' : |T ![u, w, w]| ≤ K * (|T ![u, w, w]| / (K + 1)) := by
    simpa [K, t0] using hbound0
  have hmul :
      (K + 1) * |T ![u, w, w]| ≤ K * |T ![u, w, w]| := by
    have hmul0 := mul_le_mul_of_nonneg_left hbound0' hK_pos.le
    have hrhs : (K + 1) * (K * (|T ![u, w, w]| / (K + 1))) = K * |T ![u, w, w]| := by
      field_simp [hK_pos.ne']
    rwa [hrhs] at hmul0
  nlinarith

/-- Helper for Lemma 5.1.2: once the first slot lies in the Hessian local radical, symmetry in the
last two slots forces the full mixed trilinear evaluation to vanish. -/
private lemma iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u v w : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hx : x ∈ dom)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_iter : ∀ z : E,
      |iteratedFDeriv ℝ 3 f x ![z, z, z]| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    (hu : ∀ z : E, inner ℝ u (hessian f x z) = 0) :
    iteratedFDeriv ℝ 3 f x ![u, v, w] = 0 := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  have hvv : T ![u, v, v] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (dom := dom) (Mf := Mf) (f := f) (x := x) (u := u) (w := v)
        hdom_open hcont hx hxPos hdiag_iter hu
  have hww : T ![u, w, w] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (dom := dom) (Mf := Mf) (f := f) (x := x) (u := u) (w := w)
        hdom_open hcont hx hxPos hdiag_iter hu
  have hsumZero : T ![u, v + w, v + w] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (dom := dom) (Mf := Mf) (f := f) (x := x) (u := u) (w := v + w)
        hdom_open hcont hx hxPos hdiag_iter hu
  have hsumExpand :
      T ![u, v + w, v + w] =
        T ![u, v, v] + T ![u, v, w] + T ![u, w, v] + T ![u, w, w] := by
    have hfirst :
        Function.update ![u, v, v + w] 1 (v + w) = ![u, v + w, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hsecond :
        Function.update ![u, v, v] 2 (v + w) = ![u, v, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hthird :
        Function.update ![u, w, v] 2 (v + w) = ![u, w, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hfourth :
        Function.update ![u, v, v + w] 1 v = ![u, v, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hfifth :
        Function.update ![u, v, v + w] 1 w = ![u, w, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hsix : Function.update ![u, v, v] 2 v = ![u, v, v] := by
      ext i
      fin_cases i <;> rfl
    have hseven : Function.update ![u, v, v] 2 w = ![u, v, w] := by
      ext i
      fin_cases i <;> rfl
    have height : Function.update ![u, w, v] 2 v = ![u, w, v] := by
      ext i
      fin_cases i <;> rfl
    have hnine : Function.update ![u, w, v] 2 w = ![u, w, w] := by
      ext i
      fin_cases i <;> rfl
    -- Expand the second slot first and then the third slot in each summand.
    rw [← hfirst, T.map_update_add, hfourth, hfifth,
      ← hsecond, ← hthird, T.map_update_add, T.map_update_add]
    rw [hsix, hseven, height, hnine]
    simp [add_left_comm, add_comm]
  have hswap23 :
      T ![u, w, v] = T ![u, v, w] := by
    simpa [T] using
      (iteratedFDeriv_three_swap23
        (dom := dom) (f := f) hdom_open hcont hx u w v)
  -- The `v + w` diagonal expansion leaves only the two equal cross terms, so they must vanish.
  rw [hsumExpand, hvv, hww, hswap23, zero_add, add_zero] at hsumZero
  nlinarith

/-- Helper for Lemma 5.1.2: Hessian local norms scale by the absolute value of the scalar once the
pointwise Hessian is positive semidefinite. -/
private theorem hessianLocalNorm_smul_eq_abs_of_isPositive
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) (a : ℝ) :
    ‖a • u‖[f; x] = |a| * ‖u‖[f; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian f x u) := hxPos.inner_nonneg_right u
  -- Rewrite the scaled quadratic form before taking square roots.
  calc
    ‖a • u‖[f; x] = Real.sqrt ((a * a) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (a * a) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = |a| * ‖u‖[f; x] := by
      rw [show a * a = a ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, hessianLocalNorm_def]
      ring

/-- Helper for Lemma 5.1.2: the square of the Hessian local norm satisfies the parallelogram
identity coming from the underlying Hessian quadratic form. -/
private theorem hessianLocalNorm_parallelogram_sq
    {f : E → ℝ} {x u v : E} (hxPos : (hessian f x).IsPositive) :
    ‖u + v‖[f; x] ^ (2 : ℕ) + ‖u - v‖[f; x] ^ (2 : ℕ) =
      2 * (‖u‖[f; x] ^ (2 : ℕ) + ‖v‖[f; x] ^ (2 : ℕ)) := by
  -- Expand the local norms back to the Hessian quadratic form and cancel the mixed terms.
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u + v)
      (hxPos.inner_nonneg_right (u + v))]
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u - v)
      (hxPos.inner_nonneg_right (u - v))]
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u)
      (hxPos.inner_nonneg_right u)]
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := v)
      (hxPos.inner_nonneg_right v)]
  simp [map_add, map_sub, sub_eq_add_neg, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right]
  ring

/-- Helper for Lemma 5.1.2: if the repeated direction lies in the Hessian local radical, then the
`(d,v,v)` evaluation also vanishes after swapping the first two slots. -/
private lemma iteratedFDeriv_dvv_vanishes_on_hessian_localRadical
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x d v : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hx : x ∈ dom)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_iter : ∀ z : E,
      |iteratedFDeriv ℝ 3 f x ![z, z, z]| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    (hv : ∀ z : E, inner ℝ v (hessian f x z) = 0) :
    iteratedFDeriv ℝ 3 f x ![d, v, v] = 0 := by
  have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
  -- Swap the Hessian-radical direction into the first slot, apply the stronger vanishing helper,
  -- and then swap back only at the API level.
  calc
    iteratedFDeriv ℝ 3 f x ![d, v, v]
        = iteratedFDeriv ℝ 3 f x ![v, d, v] := by
            simpa using
              (iteratedFDeriv_three_swap12
                (f := f) (x := x) (u₁ := d) (u₂ := v) (u₃ := v) hcontAt)
    _ = 0 := by
          exact
            iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
              (dom := dom) (Mf := Mf) (f := f) (x := x) (u := v) (v := d) (w := v)
              hdom_open hcont hx hxPos hdiag_iter hv

/-- Helper for Lemma 5.1.2: dividing a nonzero coefficient pair by its Euclidean radius produces
a unit-circle pair and factors that radius back out of the vector combination. -/
private lemma normModel2D_normalizeCoeffs
    {e₁ e₂ : E} {a b r : ℝ}
    (hr : r = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ))) (hr_ne : r ≠ 0) :
    a • e₁ + b • e₂ = r • ((a / r) • e₁ + (b / r) • e₂) ∧
      (a / r) ^ (2 : ℕ) + (b / r) ^ (2 : ℕ) = 1 := by
  constructor
  · -- Factor the common Euclidean radius out of the two coefficients.
    have ha : r * (a / r) = a := by
      field_simp [hr_ne]
    have hb : r * (b / r) = b := by
      field_simp [hr_ne]
    calc
      a • e₁ + b • e₂ = (r * (a / r)) • e₁ + (r * (b / r)) • e₂ := by rw [ha, hb]
      _ = r • ((a / r) • e₁) + r • ((b / r) • e₂) := by simp [smul_smul]
      _ = r • ((a / r) • e₁ + (b / r) • e₂) := by rw [smul_add]
  · -- Dividing by the Euclidean radius puts the coefficient pair on the unit circle.
    have hsq : r ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
      rw [hr]
      exact Real.sq_sqrt (by positivity)
    rw [pow_two, pow_two]
    field_simp [hr_ne]
    nlinarith [hsq]

/-- Helper for Lemma 5.1.2: on a normalized 2D Hessian model, the unresolved core estimate is the
pure unit-circle repeated-slot bound. -/
private lemma unitCircleDiagonalSampleBound
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ c s : ℝ, c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 →
      |T ![c • e₁ + s • e₂, c • e₁ + s • e₂, c • e₁ + s • e₂]| ≤ 2 * (Mf : ℝ) := by
  intro c s hunit
  have hnorm_sq : ‖c • e₁ + s • e₂‖[f; x] ^ (2 : ℕ) = 1 := by
    rw [hnorm_model, hunit]
  have hnorm_nonneg : 0 ≤ ‖c • e₁ + s • e₂‖[f; x] :=
    hessianLocalNorm_nonneg f x (c • e₁ + s • e₂)
  have hnorm_eq : ‖c • e₁ + s • e₂‖[f; x] = 1 := by
    nlinarith
  -- Specialize the diagonal cubic bound to a unit vector in the normalized 2D model.
  simpa [hnorm_eq] using hdiag (c • e₁ + s • e₂)

/-- Helper for Lemma 5.1.2: a symmetric trilinear form recovers its `(u,w,w)` coefficient from
the three diagonal samples at the `±60°` unit-circle directions around `u`. -/
private lemma symmetricTrilinear_sixtyDegreeInterpolation
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (u w : E) :
    T ![u, w, w] =
      (4 / 9 : ℝ) *
          (T ![(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w] +
            T ![(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w]) -
        (1 / 9 : ℝ) * T ![u, u, u] := by
  have hcentered :=
    symmetricTrilinear_centeredSecondDifference T hswap12 hswap23 u w (Real.sqrt 3)
  have hplusScale :
      T ![u + Real.sqrt 3 • w, u + Real.sqrt 3 • w, u + Real.sqrt 3 • w] =
        8 *
          T ![(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w] := by
    -- Rewrite the `+√3` direction as twice the normalized `+60°` unit-circle direction.
    have huv :
        u + Real.sqrt 3 • w =
          (2 : ℝ) • ((1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w) := by
      simp [smul_add, smul_smul]
      ring
    rw [huv]
    rw [trilinearApplySmulFirst, trilinearApplySmulSecond, trilinearApplySmulThird]
    ring
  have hminusScale :
      T ![u - Real.sqrt 3 • w, u - Real.sqrt 3 • w, u - Real.sqrt 3 • w] =
        8 *
          T ![(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w] := by
    -- The reflected `-60°` direction scales in the same way.
    have huv :
        u - Real.sqrt 3 • w =
          (2 : ℝ) • ((1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w) := by
      simp [smul_add, smul_smul, sub_eq_add_neg]
      ring
    rw [huv]
    rw [trilinearApplySmulFirst, trilinearApplySmulSecond, trilinearApplySmulThird]
    ring
  -- Substitute the normalized `±60°` samples into the centered second-difference identity and
  -- solve the resulting scalar equation for `T[u,w,w]`.
  rw [hplusScale, hminusScale] at hcentered
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
  have hcentered' :
      18 * T ![u, w, w] =
        8 *
          (T ![(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w] +
            T ![(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w]) -
          2 * T ![u, u, u] := by
    rw [hsqrt_sq] at hcentered
    linarith
  linarith

/-- Helper for Lemma 5.1.2: the diagonal value of a symmetric trilinear map on
`a • e₁ + b • e₂` expands into the four basis monomials. -/
private lemma symmetricTrilinear_diagonalOnTwoVectors
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (e₁ e₂ : E) (a b : ℝ) :
    T ![a • e₁ + b • e₂, a • e₁ + b • e₂, a • e₁ + b • e₂] =
      a ^ (3 : ℕ) * T ![e₁, e₁, e₁] +
        3 * a ^ (2 : ℕ) * b * T ![e₁, e₁, e₂] +
          3 * a * b ^ (2 : ℕ) * T ![e₁, e₂, e₂] +
            b ^ (3 : ℕ) * T ![e₂, e₂, e₂] := by
  -- Expand the three identical slots once and normalize the mixed monomials via symmetry.
  rw [trilinearApplyAddFirst]
  rw [trilinearApplyAddSecond, trilinearApplyAddSecond]
  rw [trilinearApplyAddThird, trilinearApplyAddThird, trilinearApplyAddThird,
    trilinearApplyAddThird]
  rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
    trilinearApplySmulThird]
  rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
    trilinearApplySmulSecond]
  rw [trilinearApplySmulFirst, trilinearApplySmulFirst, trilinearApplySmulFirst,
    trilinearApplySmulFirst, trilinearApplySmulFirst, trilinearApplySmulFirst,
    trilinearApplySmulFirst, trilinearApplySmulFirst]
  rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
    trilinearApplySmulThird]
  rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
    trilinearApplySmulSecond]
  rw [hswap23 e₁ e₂ e₁, hswap12 e₂ e₁ e₁, hswap23 e₁ e₂ e₁, hswap12 e₂ e₁ e₂,
    hswap23 e₂ e₂ e₁, hswap12 e₂ e₁ e₂]
  ring

/-- Helper for Lemma 5.1.2: a first-quadrant unit-circle coefficient pair lifts to the cubic-angle
parameters used by the three-sample interpolation identity. -/
private lemma firstQuadrantUnitCircle_hasThirdAngleParameters
    {c s : ℝ} (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s)
    (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    ∃ sa ca : ℝ,
      sa ^ (2 : ℕ) + ca ^ (2 : ℕ) = 1 ∧
        s = 4 * ca ^ (3 : ℕ) - 3 * ca ∧
          c = 3 * sa - 4 * sa ^ (3 : ℕ) := by
  let θ : ℝ := Real.arcsin c / 3
  refine ⟨Real.sin θ, Real.cos θ, ?_, ?_, ?_⟩
  · -- The lifted pair still lies on the Euclidean unit circle.
    simpa [θ] using Real.sin_sq_add_cos_sq θ
  · -- The cosine triple-angle identity recovers the second coefficient `s`.
    have hc_lower : -1 ≤ c := by nlinarith
    have hc_upper : c ≤ 1 := by nlinarith [hunit]
    have hθ_three : Real.arcsin c = 3 * θ := by
      dsimp [θ]
      ring
    have hsqrt :
        Real.sqrt (1 - c ^ (2 : ℕ)) = s := by
      apply (Real.sqrt_eq_iff_eq_sq ?_ hs_nonneg).2
      · nlinarith [hunit]
      · nlinarith [hunit]
    calc
      s = Real.sqrt (1 - c ^ (2 : ℕ)) := by symm; exact hsqrt
      _ = Real.cos (Real.arcsin c) := by symm; exact Real.cos_arcsin c
      _ = Real.cos (3 * θ) := by rw [hθ_three]
      _ = 4 * Real.cos θ ^ (3 : ℕ) - 3 * Real.cos θ := by rw [Real.cos_three_mul]
  · -- The sine triple-angle identity recovers the first coefficient `c`.
    have hc_lower : -1 ≤ c := by nlinarith
    have hc_upper : c ≤ 1 := by nlinarith [hunit]
    have hθ_three : Real.arcsin c = 3 * θ := by
      dsimp [θ]
      ring
    calc
      c = Real.sin (Real.arcsin c) := by
            symm
            exact Real.sin_arcsin hc_lower hc_upper
      _ = Real.sin (3 * θ) := by rw [hθ_three]
      _ = 3 * Real.sin θ - 4 * Real.sin θ ^ (3 : ℕ) := by rw [Real.sin_three_mul]

/-- Helper for Lemma 5.1.2: the mixed repeated-slot coefficient `T[c • e₁ + s • e₂, e₂, e₂]`
is an explicit convex combination of three diagonal unit-circle samples after a cubic-angle
reparameterization. -/
private lemma symmetricTrilinear_thirdAngleInterpolation
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    {x e₁ e₂ : E} {sa ca c s : ℝ}
    (hsq : sa ^ (2 : ℕ) + ca ^ (2 : ℕ) = 1)
    (hs : s = 4 * ca ^ (3 : ℕ) - 3 * ca)
    (hc : c = 3 * sa - 4 * sa ^ (3 : ℕ)) :
    let l₀ : ℝ := (4 * sa ^ (2 : ℕ) - 3) ^ (2 : ℕ) / 9
    let l₁ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa + Real.sqrt 3 * ca) ^ (2 : ℕ)
    let l₂ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa - Real.sqrt 3 * ca) ^ (2 : ℕ)
    let v₀ : E := sa • e₁ + ca • e₂
    let v₁ : E :=
      (-sa / 2 + (Real.sqrt 3 / 2) * ca) • e₁ + (-ca / 2 - (Real.sqrt 3 / 2) * sa) • e₂
    let v₂ : E :=
      (-sa / 2 - (Real.sqrt 3 / 2) * ca) • e₁ + (-ca / 2 + (Real.sqrt 3 / 2) * sa) • e₂
    T ![c • e₁ + s • e₂, e₂, e₂] =
      l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂] := by
  -- Route correction: rewrite everything in the fixed basis `(e₁,e₂)` and compare the four
  -- canonical basis monomials instead of reviving the rotated-frame interpolation.
  dsimp
  set l₀ : ℝ := (4 * sa ^ (2 : ℕ) - 3) ^ (2 : ℕ) / 9
  set l₁ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa + Real.sqrt 3 * ca) ^ (2 : ℕ)
  set l₂ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa - Real.sqrt 3 * ca) ^ (2 : ℕ)
  set a₁ : ℝ := -sa / 2 + (Real.sqrt 3 / 2) * ca
  set b₁ : ℝ := -ca / 2 - (Real.sqrt 3 / 2) * sa
  set a₂ : ℝ := -sa / 2 - (Real.sqrt 3 / 2) * ca
  set b₂ : ℝ := -ca / 2 + (Real.sqrt 3 / 2) * sa
  set v₀ : E := sa • e₁ + ca • e₂
  set v₁ : E := a₁ • e₁ + b₁ • e₂
  set v₂ : E := a₂ • e₁ + b₂ • e₂
  set A : ℝ := T ![e₁, e₁, e₁]
  set B : ℝ := T ![e₁, e₁, e₂]
  set C : ℝ := T ![e₁, e₂, e₂]
  set D : ℝ := T ![e₂, e₂, e₂]
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
  have hca2 : ca ^ (2 : ℕ) = 1 - sa ^ (2 : ℕ) := by
    nlinarith [hsq]
  have hca3 : ca ^ (3 : ℕ) = ca * (1 - sa ^ (2 : ℕ)) := by
    rw [show ca ^ (3 : ℕ) = ca * ca ^ (2 : ℕ) by ring, hca2]
  have hca4 : ca ^ (4 : ℕ) = (1 - sa ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [show ca ^ (4 : ℕ) = (ca ^ (2 : ℕ)) ^ (2 : ℕ) by ring, hca2]
  have hca5 : ca ^ (5 : ℕ) = ca * (1 - sa ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [show ca ^ (5 : ℕ) = ca * ca ^ (4 : ℕ) by ring, hca4]
  have hsqrt_four : (Real.sqrt 3) ^ (4 : ℕ) = 9 := by
    calc
      (Real.sqrt 3) ^ (4 : ℕ) = ((Real.sqrt 3) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 9 := by rw [hsqrt_sq]; norm_num
  have hleft :
      T ![c • e₁ + s • e₂, e₂, e₂] = c * C + s * D := by
    -- The left side only uses the canonical basis monomials with two `e₂` slots.
    rw [trilinearApplyAddFirst, trilinearApplySmulFirst, trilinearApplySmulFirst]
  have hv₀ :
      T ![v₀, v₀, v₀] =
        sa ^ (3 : ℕ) * A +
          3 * sa ^ (2 : ℕ) * ca * B +
            3 * sa * ca ^ (2 : ℕ) * C +
              ca ^ (3 : ℕ) * D := by
    -- The first sample is the direct diagonal expansion of `(sa,ca)`.
    simpa [v₀, A, B, C, D] using
      symmetricTrilinear_diagonalOnTwoVectors T hswap12 hswap23 e₁ e₂ sa ca
  have hv₁ :
      T ![v₁, v₁, v₁] =
        a₁ ^ (3 : ℕ) * A +
          3 * a₁ ^ (2 : ℕ) * b₁ * B +
            3 * a₁ * b₁ ^ (2 : ℕ) * C +
              b₁ ^ (3 : ℕ) * D := by
    -- The second sample uses the same diagonal expansion at the rotated coefficients.
    simpa [v₁, a₁, b₁, A, B, C, D] using
      symmetricTrilinear_diagonalOnTwoVectors T hswap12 hswap23 e₁ e₂ a₁ b₁
  have hv₂ :
      T ![v₂, v₂, v₂] =
        a₂ ^ (3 : ℕ) * A +
          3 * a₂ ^ (2 : ℕ) * b₂ * B +
            3 * a₂ * b₂ ^ (2 : ℕ) * C +
              b₂ ^ (3 : ℕ) * D := by
    -- The third sample is the reflected rotated coefficient pair.
    simpa [v₂, a₂, b₂, A, B, C, D] using
      symmetricTrilinear_diagonalOnTwoVectors T hswap12 hswap23 e₁ e₂ a₂ b₂
  have hA :
      l₀ * sa ^ (3 : ℕ) + l₁ * a₁ ^ (3 : ℕ) + l₂ * a₂ ^ (3 : ℕ) = 0 := by
    -- The `T[e₁,e₁,e₁]` coefficient cancels from the three-sample combination.
    simp [l₀, l₁, l₂, a₁, a₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca4, hca2]
    ring_nf
  have hB :
      l₀ * (3 * sa ^ (2 : ℕ) * ca) +
        l₁ * (3 * a₁ ^ (2 : ℕ) * b₁) +
          l₂ * (3 * a₂ ^ (2 : ℕ) * b₂) = 0 := by
    -- The `T[e₁,e₁,e₂]` coefficient cancels for the same reason.
    simp [l₀, l₁, l₂, a₁, b₁, a₂, b₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca5, hca3]
    ring_nf
  have hC :
      l₀ * (3 * sa * ca ^ (2 : ℕ)) +
        l₁ * (3 * a₁ * b₁ ^ (2 : ℕ)) +
          l₂ * (3 * a₂ * b₂ ^ (2 : ℕ)) = c := by
    -- The surviving `T[e₁,e₂,e₂]` coefficient is exactly the cubic-angle sine expression.
    rw [hc]
    simp [l₀, l₁, l₂, a₁, b₁, a₂, b₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca4, hca2]
    ring_nf
  have hD :
      l₀ * ca ^ (3 : ℕ) + l₁ * b₁ ^ (3 : ℕ) + l₂ * b₂ ^ (3 : ℕ) = s := by
    -- The surviving `T[e₂,e₂,e₂]` coefficient is exactly the cubic-angle cosine expression.
    rw [hs]
    simp [l₀, l₁, l₂, b₁, b₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca5, hca3]
    ring_nf
  rw [hleft, hv₀, hv₁, hv₂]
  -- Regroup the diagonal expansions by the four canonical basis monomials and use the scalar
  -- coefficient identities proved above.
  have hcollect :
      l₀ * (sa ^ (3 : ℕ) * A + 3 * sa ^ (2 : ℕ) * ca * B + 3 * sa * ca ^ (2 : ℕ) * C +
          ca ^ (3 : ℕ) * D) +
        l₁ * (a₁ ^ (3 : ℕ) * A + 3 * a₁ ^ (2 : ℕ) * b₁ * B + 3 * a₁ * b₁ ^ (2 : ℕ) * C +
          b₁ ^ (3 : ℕ) * D) +
          l₂ * (a₂ ^ (3 : ℕ) * A + 3 * a₂ ^ (2 : ℕ) * b₂ * B +
            3 * a₂ * b₂ ^ (2 : ℕ) * C + b₂ ^ (3 : ℕ) * D) =
        (l₀ * sa ^ (3 : ℕ) + l₁ * a₁ ^ (3 : ℕ) + l₂ * a₂ ^ (3 : ℕ)) * A +
          (l₀ * (3 * sa ^ (2 : ℕ) * ca) + l₁ * (3 * a₁ ^ (2 : ℕ) * b₁) +
            l₂ * (3 * a₂ ^ (2 : ℕ) * b₂)) * B +
              (l₀ * (3 * sa * ca ^ (2 : ℕ)) + l₁ * (3 * a₁ * b₁ ^ (2 : ℕ)) +
                l₂ * (3 * a₂ * b₂ ^ (2 : ℕ))) * C +
                  (l₀ * ca ^ (3 : ℕ) + l₁ * b₁ ^ (3 : ℕ) + l₂ * b₂ ^ (3 : ℕ)) * D := by
    ring
  rw [hcollect, hA, hB, hC, hD]
  ring

/-- Helper for Lemma 5.1.2: in the first-quadrant unit-circle case, the mixed repeated-slot term
is bounded by the diagonal cubic bound through the three-sample interpolation formula. -/
private lemma symmetricTrilinear_unitCircle_dvvBound_onNormModel2D_nonneg
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    {c s : ℝ} (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s)
    (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    |T ![c • e₁ + s • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) := by
  obtain ⟨sa, ca, hsq, hs, hc⟩ :=
    firstQuadrantUnitCircle_hasThirdAngleParameters hc_nonneg hs_nonneg hunit
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
  have hca2 : ca ^ (2 : ℕ) = 1 - sa ^ (2 : ℕ) := by
    nlinarith [hsq]
  set l₀ : ℝ := (4 * sa ^ (2 : ℕ) - 3) ^ (2 : ℕ) / 9
  set l₁ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa + Real.sqrt 3 * ca) ^ (2 : ℕ)
  set l₂ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa - Real.sqrt 3 * ca) ^ (2 : ℕ)
  set a₁ : ℝ := -sa / 2 + (Real.sqrt 3 / 2) * ca
  set b₁ : ℝ := -ca / 2 - (Real.sqrt 3 / 2) * sa
  set a₂ : ℝ := -sa / 2 - (Real.sqrt 3 / 2) * ca
  set b₂ : ℝ := -ca / 2 + (Real.sqrt 3 / 2) * sa
  set v₀ : E := sa • e₁ + ca • e₂
  set v₁ : E := a₁ • e₁ + b₁ • e₂
  set v₂ : E := a₂ • e₁ + b₂ • e₂
  have hv₀_unit : sa ^ (2 : ℕ) + ca ^ (2 : ℕ) = 1 := hsq
  have hv₁_unit : a₁ ^ (2 : ℕ) + b₁ ^ (2 : ℕ) = 1 := by
    -- The second sample is a Euclidean rotation of `(sa,ca)`.
    simp [a₁, b₁]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hv₂_unit : a₂ ^ (2 : ℕ) + b₂ ^ (2 : ℕ) = 1 := by
    -- The third sample is the opposite Euclidean rotation of `(sa,ca)`.
    simp [a₂, b₂]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hbound₀ :
      |T ![v₀, v₀, v₀]| ≤ 2 * (Mf : ℝ) := by
    -- Each diagonal sample lies on the normalized unit circle, so the diagonal bound loses the
    -- norm factor.
    simpa [v₀] using unitCircleDiagonalSampleBound T Mf f hnorm_model hdiag sa ca hv₀_unit
  have hbound₁ :
      |T ![v₁, v₁, v₁]| ≤ 2 * (Mf : ℝ) := by
    simpa [v₁] using unitCircleDiagonalSampleBound T Mf f hnorm_model hdiag a₁ b₁ hv₁_unit
  have hbound₂ :
      |T ![v₂, v₂, v₂]| ≤ 2 * (Mf : ℝ) := by
    simpa [v₂] using unitCircleDiagonalSampleBound T Mf f hnorm_model hdiag a₂ b₂ hv₂_unit
  have hl₀_nonneg : 0 ≤ l₀ := by positivity
  have hl₁_nonneg : 0 ≤ l₁ := by positivity
  have hl₂_nonneg : 0 ≤ l₂ := by positivity
  have hweights :
      l₀ + l₁ + l₂ = 1 := by
    -- The three interpolation weights form a partition of unity.
    simp [l₀, l₁, l₂]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hinterp :=
    symmetricTrilinear_thirdAngleInterpolation T hswap12 hswap23
      (x := x) (e₁ := e₁) (e₂ := e₂) (sa := sa) (ca := ca) (c := c) (s := s) hsq hs hc
  have hinterp' :
      T ![c • e₁ + s • e₂, e₂, e₂] =
        l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂] := by
    simpa [l₀, l₁, l₂, v₀, v₁, v₂] using hinterp
  rw [hinterp']
  have habs₀ : |l₀ * T ![v₀, v₀, v₀]| = l₀ * |T ![v₀, v₀, v₀]| := by
    rw [abs_mul, abs_of_nonneg hl₀_nonneg]
  have habs₁ : |l₁ * T ![v₁, v₁, v₁]| = l₁ * |T ![v₁, v₁, v₁]| := by
    rw [abs_mul, abs_of_nonneg hl₁_nonneg]
  have habs₂ : |l₂ * T ![v₂, v₂, v₂]| = l₂ * |T ![v₂, v₂, v₂]| := by
    rw [abs_mul, abs_of_nonneg hl₂_nonneg]
  have htri :
      |l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]|
        ≤ |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]| := by
    calc
      |l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]|
          = |l₀ * T ![v₀, v₀, v₀] + (l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂])| := by
              ring_nf
      _ ≤ |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]| :=
            abs_add_le _ _
      _ ≤ |l₀ * T ![v₀, v₀, v₀]| +
            (|l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]|) := by
              gcongr
              exact abs_add_le _ _
      _ = |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]| := by
            simp [add_assoc]
  calc
    |l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]|
        ≤ |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]| :=
          htri
    _ = l₀ * |T ![v₀, v₀, v₀]| + l₁ * |T ![v₁, v₁, v₁]| + l₂ * |T ![v₂, v₂, v₂]| := by
          rw [habs₀, habs₁, habs₂]
    _ ≤ l₀ * (2 * (Mf : ℝ)) + l₁ * (2 * (Mf : ℝ)) + l₂ * (2 * (Mf : ℝ)) := by
          gcongr
    _ = (l₀ + l₁ + l₂) * (2 * (Mf : ℝ)) := by ring
    _ = 2 * (Mf : ℝ) := by rw [hweights]; ring

/-- Helper for Lemma 5.1.2: reduce the arbitrary-sign unit-circle case to the first-quadrant
case by flipping the basis vectors. -/
private lemma symmetricTrilinear_unitCircle_dvvBound_onNormModel2D
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ c s : ℝ, c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 →
      |T ![c • e₁ + s • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) := by
  intro c s hunit
  let σc : ℝ := if 0 ≤ c then 1 else -1
  let σs : ℝ := if 0 ≤ s then 1 else -1
  let e₁' : E := σc • e₁
  let e₂' : E := σs • e₂
  have hσc_sq : σc ^ (2 : ℕ) = 1 := by
    dsimp [σc]
    split_ifs <;> norm_num
  have hσs_sq : σs ^ (2 : ℕ) = 1 := by
    dsimp [σs]
    split_ifs <;> norm_num
  have hc_nonneg : 0 ≤ |c| := abs_nonneg c
  have hs_nonneg : 0 ≤ |s| := abs_nonneg s
  have hunit_abs : |c| ^ (2 : ℕ) + |s| ^ (2 : ℕ) = 1 := by
    simpa [pow_two] using hunit
  have hc_sign : c = σc * |c| := by
    dsimp [σc]
    split_ifs with hc
    · rw [abs_of_nonneg hc]
      ring
    · have hc_lt : c < 0 := lt_of_not_ge hc
      rw [abs_of_neg hc_lt]
      ring
  have hs_sign : s = σs * |s| := by
    dsimp [σs]
    split_ifs with hs
    · rw [abs_of_nonneg hs]
      ring
    · have hs_lt : s < 0 := lt_of_not_ge hs
      rw [abs_of_neg hs_lt]
      ring
  have hnorm_model' :
      ∀ a b : ℝ, ‖a • e₁' + b • e₂'‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    intro a b
    -- Flipping basis-vector signs preserves the same normalized 2D norm model.
    dsimp [e₁', e₂']
    calc
      ‖a • (σc • e₁) + b • (σs • e₂)‖[f; x] ^ (2 : ℕ)
          = ‖(a * σc) • e₁ + (b * σs) • e₂‖[f; x] ^ (2 : ℕ) := by
              simp [smul_smul]
      _ = (a * σc) ^ (2 : ℕ) + (b * σs) ^ (2 : ℕ) := hnorm_model (a * σc) (b * σs)
      _ = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
            nlinarith [hσc_sq, hσs_sq]
  have hrew :
      T ![|c| • e₁' + |s| • e₂', e₂', e₂'] = T ![c • e₁ + s • e₂, e₂, e₂] := by
    -- The first slot is unchanged by the signed basis flip, and the repeated slots square away
    -- the sign on `e₂`.
    dsimp [e₁', e₂']
    rw [trilinearApplySmulSecond, trilinearApplySmulThird]
    have hfirst :
        |c| • (σc • e₁) + |s| • (σs • e₂) = c • e₁ + s • e₂ := by
      rw [smul_smul, smul_smul, mul_comm |c| σc, mul_comm |s| σs, ← hc_sign, ← hs_sign]
    rw [hfirst]
    calc
      σs * (σs * T ![c • e₁ + s • e₂, e₂, e₂])
          = (σs ^ (2 : ℕ)) * T ![c • e₁ + s • e₂, e₂, e₂] := by ring
      _ = T ![c • e₁ + s • e₂, e₂, e₂] := by rw [hσs_sq]; ring
  -- Apply the explicit three-sample interpolation bound after moving to the first quadrant.
  have hbound_abs :
      |T ![|c| • e₁' + |s| • e₂', e₂', e₂']| ≤ 2 * (Mf : ℝ) :=
    symmetricTrilinear_unitCircle_dvvBound_onNormModel2D_nonneg
      (T := T) (e₁ := e₁') (e₂ := e₂')
      hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model' hdiag
      hc_nonneg hs_nonneg hunit_abs
  rw [← hrew]
  exact hbound_abs

/-- Helper for Lemma 5.1.2: after normalizing the coefficients to the unit circle, the pure 2D
estimate immediately rescales back to arbitrary coefficients. -/
private lemma symmetricTrilinear_dvvBound_ofDiagonalBound_onNormModel2D
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ a b : ℝ,
      |T ![a • e₁ + b • e₂, e₂, e₂]| ≤
        2 * (Mf : ℝ) * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  intro a b
  let r : ℝ := Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ))
  by_cases hr : r = 0
  · have hab : a ^ (2 : ℕ) + b ^ (2 : ℕ) = 0 := by
      have hsq : r ^ (2 : ℕ) = 0 := by simpa [hr]
      dsimp [r] at hsq
      rw [Real.sq_sqrt (by positivity)] at hsq
      exact hsq
    have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, hab]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, hab]
    have hzeroVec : T ![0, e₂, e₂] = 0 := by
      simpa using trilinearApplySmulFirst T 0 e₁ e₂ e₂
    -- In the zero-radius branch, both coefficients vanish and the bound is immediate.
    have hleft : |T ![a • e₁ + b • e₂, e₂, e₂]| = 0 := by
      rw [ha, hb]
      simp [hzeroVec]
    rw [hleft]
    simp [ha, hb]
  · obtain ⟨hvec, hunit⟩ :=
      normModel2D_normalizeCoeffs (e₁ := e₁) (e₂ := e₂) (a := a) (b := b) (r := r) rfl hr
    have hunitBound :
        |T ![(a / r) • e₁ + (b / r) • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) :=
      symmetricTrilinear_unitCircle_dvvBound_onNormModel2D
        (T := T) (e₁ := e₁) (e₂ := e₂)
        hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model hdiag
        (a / r) (b / r) hunit
    -- Pull the scalar `r` back out of the first slot and use that `r` is a square root.
    calc
      |T ![a • e₁ + b • e₂, e₂, e₂]|
          = |T ![r • ((a / r) • e₁ + (b / r) • e₂), e₂, e₂]| := by rw [hvec]
      _ = |r * T ![(a / r) • e₁ + (b / r) • e₂, e₂, e₂]| := by
            rw [trilinearApplySmulFirst]
      _ = |r| * |T ![(a / r) • e₁ + (b / r) • e₂, e₂, e₂]| := by rw [abs_mul]
      _ ≤ |r| * (2 * (Mf : ℝ)) := by
            gcongr
      _ = 2 * (Mf : ℝ) * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
            rw [abs_of_nonneg (by
              dsimp [r]
              exact Real.sqrt_nonneg _)]
            dsimp [r]
            ring

/-- Helper for Lemma 5.1.2: once the sharp repeated-slot estimate
`|T[u₁, v, v]| ≤ C ‖u₁‖[f; x] ‖v‖[f; x]^2` is available, bilinear polarization in the last two
slots upgrades it to the full mixed bound whenever the last two local norms are nonzero. -/
private lemma iteratedFDeriv_mixed_bound_of_dvv_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u₁ u₂ u₃ : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hx : x ∈ dom)
    (hxPos : (hessian f x).IsPositive)
    (hu₂ : ‖u₂‖[f; x] ≠ 0)
    (hu₃ : ‖u₃‖[f; x] ≠ 0)
    (hdvv : ∀ d v : E,
      |iteratedFDeriv ℝ 3 f x ![d, v, v]| ≤
        2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ)) :
    |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
      2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  let n₂ : ℝ := ‖u₂‖[f; x]
  let n₃ : ℝ := ‖u₃‖[f; x]
  have hn₂_pos : 0 < n₂ := by
    dsimp [n₂]
    exact lt_of_le_of_ne (hessianLocalNorm_nonneg f x u₂) (by simpa using hu₂.symm)
  have hn₃_pos : 0 < n₃ := by
    dsimp [n₃]
    exact lt_of_le_of_ne (hessianLocalNorm_nonneg f x u₃) (by simpa using hu₃.symm)
  let a : ℝ := Real.sqrt (n₃ / n₂)
  let b : ℝ := Real.sqrt (n₂ / n₃)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg _
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact Real.sqrt_nonneg _
  have ha_sq : a ^ (2 : ℕ) = n₃ / n₂ := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have hb_sq : b ^ (2 : ℕ) = n₂ / n₃ := by
    dsimp [b]
    rw [Real.sq_sqrt]
    positivity
  have hab_sq : (a * b) ^ (2 : ℕ) = 1 := by
    calc
      (a * b) ^ (2 : ℕ) = a ^ (2 : ℕ) * b ^ (2 : ℕ) := by ring
      _ = (n₃ / n₂) * (n₂ / n₃) := by rw [ha_sq, hb_sq]
      _ = 1 := by field_simp [hn₂_pos.ne', hn₃_pos.ne']
  have hab_nonneg : 0 ≤ a * b := by positivity
  have hab : a * b = 1 := by
    nlinarith [hab_sq]
  have hswap23 :
      ∀ d v w : E, T ![d, v, w] = T ![d, w, v] := by
    intro d v w
    simpa [T] using
      iteratedFDeriv_three_swap23
        (dom := dom) (f := f) hdom_open hcont hx d v w
  have hpolar :
      T ![u₁, a • u₂ + b • u₃, a • u₂ + b • u₃] -
          T ![u₁, a • u₂ - b • u₃, a • u₂ - b • u₃] =
        4 * (a * b) * T ![u₁, u₂, u₃] := by
    have hplus :
        T ![u₁, a • u₂ + b • u₃, a • u₂ + b • u₃] =
          a ^ (2 : ℕ) * T ![u₁, u₂, u₂] +
            a * b * T ![u₁, u₂, u₃] +
              a * b * T ![u₁, u₃, u₂] +
                b ^ (2 : ℕ) * T ![u₁, u₃, u₃] := by
      -- Expand the two quadratic slots and collect the four monomials.
      rw [trilinearApplyAddSecond, trilinearApplyAddThird, trilinearApplyAddThird]
      rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
        trilinearApplySmulThird]
      rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
        trilinearApplySmulSecond]
      ring
    have hminus :
        T ![u₁, a • u₂ - b • u₃, a • u₂ - b • u₃] =
          a ^ (2 : ℕ) * T ![u₁, u₂, u₂] -
            a * b * T ![u₁, u₂, u₃] -
              a * b * T ![u₁, u₃, u₂] +
                b ^ (2 : ℕ) * T ![u₁, u₃, u₃] := by
      -- The reflected quadratic slot flips only the cross terms.
      rw [show a • u₂ - b • u₃ = a • u₂ + (-b) • u₃ by simp [sub_eq_add_neg]]
      rw [trilinearApplyAddSecond, trilinearApplyAddThird, trilinearApplyAddThird]
      rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
        trilinearApplySmulThird]
      rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
        trilinearApplySmulSecond]
      ring
    rw [hplus, hminus, hswap23 u₁ u₃ u₂]
    ring
  have hnorm_a : ‖a • u₂‖[f; x] = a * n₂ := by
    -- The chosen rescaling is nonnegative, so the absolute value disappears.
    dsimp [n₂]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (x := x) (u := u₂) hxPos]
    simp [abs_of_nonneg ha_nonneg]
  have hnorm_b : ‖b • u₃‖[f; x] = b * n₃ := by
    dsimp [n₃]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (x := x) (u := u₃) hxPos]
    simp [abs_of_nonneg hb_nonneg]
  have hnorm_sum :
      ‖a • u₂ + b • u₃‖[f; x] ^ (2 : ℕ) + ‖a • u₂ - b • u₃‖[f; x] ^ (2 : ℕ) =
        4 * n₂ * n₃ := by
    have hpar :=
      hessianLocalNorm_parallelogram_sq
        (f := f) (x := x) (u := a • u₂) (v := b • u₃) hxPos
    rw [hnorm_a, hnorm_b] at hpar
    calc
      ‖a • u₂ + b • u₃‖[f; x] ^ (2 : ℕ) + ‖a • u₂ - b • u₃‖[f; x] ^ (2 : ℕ)
          = 2 * ((a * n₂) ^ (2 : ℕ) + (b * n₃) ^ (2 : ℕ)) := hpar
      _ = 4 * n₂ * n₃ := by
            calc
              2 * ((a * n₂) ^ (2 : ℕ) + (b * n₃) ^ (2 : ℕ))
                  = 2 * (a ^ (2 : ℕ) * n₂ ^ (2 : ℕ) + b ^ (2 : ℕ) * n₃ ^ (2 : ℕ)) := by
                      ring
              _ = 2 * ((n₃ / n₂) * n₂ ^ (2 : ℕ) + (n₂ / n₃) * n₃ ^ (2 : ℕ)) := by
                    rw [ha_sq, hb_sq]
              _ = 4 * n₂ * n₃ := by
                    field_simp [pow_two, hn₂_pos.ne', hn₃_pos.ne']
                    ring
  have hfour :
      |4 * T ![u₁, u₂, u₃]| ≤
        8 * (Mf : ℝ) * ‖u₁‖[f; x] * n₂ * n₃ := by
    have hpolar' :
        T ![u₁, a • u₂ + b • u₃, a • u₂ + b • u₃] -
            T ![u₁, a • u₂ - b • u₃, a • u₂ - b • u₃] =
          4 * T ![u₁, u₂, u₃] := by
      simpa [hab] using hpolar
    rw [← hpolar']
    calc
      |T ![u₁, a • u₂ + b • u₃, a • u₂ + b • u₃] -
          T ![u₁, a • u₂ - b • u₃, a • u₂ - b • u₃]|
          ≤ |T ![u₁, a • u₂ + b • u₃, a • u₂ + b • u₃]| +
              |T ![u₁, a • u₂ - b • u₃, a • u₂ - b • u₃]| := by
                simpa using
                  (abs_sub_le (T ![u₁, a • u₂ + b • u₃, a • u₂ + b • u₃]) 0
                    (T ![u₁, a • u₂ - b • u₃, a • u₂ - b • u₃]))
      _ ≤ 2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖a • u₂ + b • u₃‖[f; x] ^ (2 : ℕ) +
            2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖a • u₂ - b • u₃‖[f; x] ^ (2 : ℕ) := by
          gcongr
          · exact hdvv u₁ (a • u₂ + b • u₃)
          · exact hdvv u₁ (a • u₂ - b • u₃)
      _ = 2 * (Mf : ℝ) * ‖u₁‖[f; x] *
            (‖a • u₂ + b • u₃‖[f; x] ^ (2 : ℕ) +
              ‖a • u₂ - b • u₃‖[f; x] ^ (2 : ℕ)) := by ring
      _ = 8 * (Mf : ℝ) * ‖u₁‖[f; x] * n₂ * n₃ := by rw [hnorm_sum]; ring
  have hfour' :
      4 * |T ![u₁, u₂, u₃]| ≤
        8 * (Mf : ℝ) * ‖u₁‖[f; x] * n₂ * n₃ := by
    have hleft : |4 * T ![u₁, u₂, u₃]| = 4 * |T ![u₁, u₂, u₃]| := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num)]
    rwa [hleft] at hfour
  dsimp [T, n₂, n₃] at hfour' ⊢
  nlinarith [hfour']

/-- Helper for Lemma 5.1.2: after the radical-vanishing lemmas are in place, the only remaining
input is the sharp quotient-Hilbert estimate for the repeated-slot pattern
`|T[d, v, v]| ≤ C ‖d‖ ‖v‖²`. -/
private lemma iteratedFDeriv_dvv_bound_of_diagonal_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hx : x ∈ dom)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_iter : ∀ z : E,
      |iteratedFDeriv ℝ 3 f x ![z, z, z]| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ d v : E,
      |iteratedFDeriv ℝ 3 f x ![d, v, v]| ≤
        2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by
  intro d v
  have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
  by_cases hd : ‖d‖[f; x] = 0
  · have hd_ann :
        ∀ z : E, inner ℝ d (hessian f x z) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := d) hxPos).1 hd
    have hzero :
        iteratedFDeriv ℝ 3 f x ![d, v, v] = 0 :=
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (dom := dom) (Mf := Mf) (f := f) (x := x) (u := d) (w := v)
        hdom_open hcont hx hxPos hdiag_iter hd_ann
    -- Once the first slot is radical, the mixed third derivative is zero and the target bound is
    -- immediate because the right-hand side also vanishes.
    simpa [hzero, hd]
  by_cases hv : ‖v‖[f; x] = 0
  · have hv_ann :
        ∀ z : E, inner ℝ v (hessian f x z) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := v) hxPos).1 hv
    have hzero :
        iteratedFDeriv ℝ 3 f x ![d, v, v] = 0 :=
      iteratedFDeriv_dvv_vanishes_on_hessian_localRadical
        (dom := dom) (Mf := Mf) (f := f) (x := x) (d := d) (v := v)
        hdom_open hcont hx hxPos hdiag_iter hv_ann
    -- The repeated-slot radical case is the same after one symmetry swap.
    simpa [hzero, hv]
  have hd_pos : 0 < ‖d‖[f; x] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f x d) (by
      intro hzero
      exact hd hzero.symm)
  have hv_pos : 0 < ‖v‖[f; x] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f x v) (by
      intro hzero
      exact hv hzero.symm)
  let α : ℝ := inner ℝ d (hessian f x v) / ‖v‖[f; x] ^ (2 : ℕ)
  let w : E := d - α • v
  have hsplit :
      inner ℝ w (hessian f x v) = 0 ∧
        ‖d‖[f; x] ^ (2 : ℕ) = ‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
    simpa [α, w] using
      hessianProjectionSplit (f := f) (x := x) (d := d) (v := v) hxPos hv
  obtain ⟨horth, hpyth⟩ := hsplit
  have hd_eq : d = w + α • v := by
    -- Rewrite the original direction into the orthogonal residual plus the `v`-component.
    dsimp [w]
    abel_nf
  by_cases hw : ‖w‖[f; x] = 0
  · have hw_ann :
        ∀ z : E, inner ℝ w (hessian f x z) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := w) hxPos).1 hw
    have hw_zero :
        iteratedFDeriv ℝ 3 f x ![w, v, v] = 0 :=
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (dom := dom) (Mf := Mf) (f := f) (x := x) (u := w) (w := v)
        hdom_open hcont hx hxPos hdiag_iter hw_ann
    have hd_abs : ‖d‖[f; x] = |α| * ‖v‖[f; x] := by
      have hd_sq :
          ‖d‖[f; x] ^ (2 : ℕ) = (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
        simpa [hw] using hpyth
      have hsqrt := congrArg Real.sqrt hd_sq
      simpa [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (hessianLocalNorm_nonneg f x d),
        abs_of_nonneg (hessianLocalNorm_nonneg f x v)] using hsqrt
    -- Once the residual is radical, only the diagonal `v` contribution survives.
    calc
      |iteratedFDeriv ℝ 3 f x ![d, v, v]|
          = |iteratedFDeriv ℝ 3 f x ![w + α • v, v, v]| := by rw [hd_eq]
      _ = |iteratedFDeriv ℝ 3 f x ![w, v, v] + iteratedFDeriv ℝ 3 f x ![α • v, v, v]| := by
            rw [trilinearApplyAddFirst]
      _ = |α * iteratedFDeriv ℝ 3 f x ![v, v, v]| := by
            rw [hw_zero, trilinearApplySmulFirst]
            simp
      _ = |α| * |iteratedFDeriv ℝ 3 f x ![v, v, v]| := by rw [abs_mul]
      _ ≤ |α| * (2 * (Mf : ℝ) * ‖v‖[f; x] ^ (3 : ℕ)) := by
            gcongr
            exact hdiag_iter v
      _ = 2 * (Mf : ℝ) * (|α| * ‖v‖[f; x]) * ‖v‖[f; x] ^ (2 : ℕ) := by
            ring
      _ = 2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by
            rw [← hd_abs]
  have hw_pos : 0 < ‖w‖[f; x] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f x w) (by
      intro hzero
      exact hw hzero.symm)
  let e₁ : E := (‖w‖[f; x])⁻¹ • w
  let e₂ : E := (‖v‖[f; x])⁻¹ • v
  have he₁_norm : ‖e₁‖[f; x] = 1 := by
    -- Normalize the nonradical residual direction.
    dsimp [e₁]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (x := x) (u := w) hxPos]
    simp [abs_of_pos (inv_pos.mpr hw_pos), hw_pos.ne']
  have he₂_norm : ‖e₂‖[f; x] = 1 := by
    -- Normalize the original repeated direction.
    dsimp [e₂]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (x := x) (u := v) hxPos]
    simp [abs_of_pos (inv_pos.mpr hv_pos), hv_pos.ne']
  have he₁e₂_orth : inner ℝ e₁ (hessian f x e₂) = 0 := by
    -- The normalized pair remains orthogonal for the Hessian bilinear form.
    simp [e₁, e₂, inner_smul_left, inner_smul_right, horth]
  have hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) :=
    hessianLocalNorm_sq_of_localOrthonormalPair
      (f := f) (x := x) (e₁ := e₁) (e₂ := e₂) hxPos he₁_norm he₂_norm he₁e₂_orth
  have hw_scale : ‖w‖[f; x] • e₁ = w := by
    -- Rescaling the normalized residual recovers the original residual vector.
    dsimp [e₁]
    rw [smul_smul, mul_inv_cancel₀ hw_pos.ne', one_smul]
  have hv_scale : (α * ‖v‖[f; x]) • e₂ = α • v := by
    -- Rescaling the normalized repeated direction recovers its original `α`-multiple.
    dsimp [e₂]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hv_pos.ne', mul_one]
  have hd_model :
      d = ‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂ := by
    -- The orthogonal split is now expressed in the normalized local-orthonormal basis.
    calc
      d = w + α • v := hd_eq
      _ = ‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂ := by
            rw [hw_scale, hv_scale]
  have hv_scale' : ‖v‖[f; x] • e₂ = v := by
    -- Rescaling the normalized repeated direction recovers the original repeated vector.
    dsimp [e₂]
    rw [smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  have hswap12 :
      ∀ a b c : E, T ![a, b, c] = T ![b, a, c] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap12
        (f := f) (x := x) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hswap23 :
      ∀ a b c : E, T ![a, b, c] = T ![a, c, b] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap23
        (dom := dom) (f := f) hdom_open hcont hx a b c
  have hmodel_bound :
      |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, e₂, e₂]| ≤
        2 * (Mf : ℝ) *
          Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ)) :=
    symmetricTrilinear_dvvBound_ofDiagonalBound_onNormModel2D
      (T := T) (e₁ := e₁) (e₂ := e₂)
      hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model hdiag_iter
      ‖w‖[f; x] (α * ‖v‖[f; x])
  have hroot :
      Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ)) = ‖d‖[f; x] := by
    -- The orthogonal decomposition identifies the Euclidean model radius with `‖d‖[f; x]`.
    have hsqrt := congrArg Real.sqrt hpyth.symm
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (hessianLocalNorm_nonneg f x d)] using hsqrt
  -- Reduce the original point to the normalized 2D model and then rescale back.
  calc
    |iteratedFDeriv ℝ 3 f x ![d, v, v]| = |T ![d, v, v]| := by rfl
    _ = |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, v, v]| := by rw [hd_model]
    _ = |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, ‖v‖[f; x] • e₂, ‖v‖[f; x] • e₂]| := by
          have hslots :
              ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, v, v] =
                ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂,
                  ‖v‖[f; x] • e₂, ‖v‖[f; x] • e₂] := by
            ext i
            fin_cases i <;> simp [hv_scale']
          rw [hslots]
    _ = |‖v‖[f; x] * (‖v‖[f; x] *
          T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, e₂, e₂])| := by
          rw [trilinearApplySmulSecond, trilinearApplySmulThird]
    _ = ‖v‖[f; x] ^ (2 : ℕ) *
          |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, e₂, e₂]| := by
          simp [pow_two, abs_of_nonneg (hessianLocalNorm_nonneg f x v), mul_assoc, mul_comm]
    _ ≤ ‖v‖[f; x] ^ (2 : ℕ) *
          (2 * (Mf : ℝ) *
            Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ))) := by
          gcongr
    _ = 2 * (Mf : ℝ) *
          Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ)) *
            ‖v‖[f; x] ^ (2 : ℕ) := by
          ring
    _ = 2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by rw [hroot]

/-
Lemma 5.1.2 lies in the chapter's self-concordance / higher-derivative multilinear domain.

Sampled owner declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the chapter owner for the Hessian operator;
* `hessianLocalNorm` and its notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`;
* `thirdDirectionalDerivative_eq_iteratedFDeriv` from `Chap05/Definition_5_0_10`, the canonical
  bridge from the diagonal third directional derivative to the trilinear third Fréchet derivative;
* `(hessian f x).IsPositive`, the canonical pointwise Hessian-positivity owner used throughout
  Chapter 5 instead of a raw quadratic-form semidefiniteness binder;
* `ContinuousMultilinearMap.le_opNorm`, the canonical multilinear operator-norm estimate in
  mathlib.

Source/core/bridge triage:
* source-facing: the diagonal cubic self-concordance bound;
* core/canonical: the trilinear map `iteratedFDeriv ℝ 3 f x`;
* bridge/view: this equivalence between the diagonal bound and the full trilinear estimate.

Primitive data:
* the objective `f`;
* the domain point `x`;
* the pointwise Hessian positivity owner `(hessian f x).IsPositive`;
* the third Fréchet derivative of `f`.

Derived API:
* the source-facing diagonal bound `|D³f(x)[u, u, u]| ≤ 2 M_f ‖u‖[f; x]^3`;
* the Hessian quadratic-form nonnegativity needed to interpret `‖u‖[f; x]`;
* the full trilinear estimate with respect to the same local norm.

This file keeps the source-facing diagonal statement, but rewrites the public surface through the
chapter owners `hessian`, `thirdDirectionalDerivative`, and `‖u‖[f; x]` instead of duplicating
their raw formulas. The old raw pointwise semidefiniteness binder is replaced by the canonical
owner `(hessian f x).IsPositive`. Since the bridge to `iteratedFDeriv` is pointwise, the domain is
kept open so that `ContDiffOn ℝ 3 f dom` upgrades to `ContDiffAt ℝ 3 f x` for `x ∈ dom`. -/

-- Proof sketch: for the forward direction, apply the norm equality for symmetric trilinear forms
-- on the Hessian-induced inner-product space at each `x` to pass from the diagonal cubic bound to
-- the full multilinear operator-norm bound, then rescale by the three local Hessian norms. For
-- the reverse direction, specialize the trilinear estimate to `u₁ = u₂ = u₃ = u`.
/-- Lemma 5.1.2: for a `C³` function with positive-semidefinite Hessian on an open set `dom`, the
diagonal cubic bound in the definition of `M_f`-self-concordance is equivalent to the full
trilinear estimate on the third derivative. -/
theorem selfConcordant_diagonal_bound_iff_trilinear_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hH : ∀ {x : E} (hx : x ∈ dom), (hessian f x).IsPositive) :
    (∀ {x : E} (hx : x ∈ dom) (u : E),
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) ↔
      ∀ {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E),
        |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
          2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := by
  constructor
  · intro hdiag x hx u₁ u₂ u₃
    -- Route correction: the pointwise rewrite and `C³`-symmetry are in place; the remaining gap is
    -- the sharp Banach-type diagonal-to-mixed estimate for symmetric trilinear forms over the
    -- Hessian local seminorm.
    have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
    have hxPos : (hessian f x).IsPositive := hH hx
    have hdiagAt := iteratedFDeriv_diagonal_bound_at_point hdom_open hcont hdiag hx
    have hswap12 :
        iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
          iteratedFDeriv ℝ 3 f x ![u₂, u₁, u₃] :=
      iteratedFDeriv_three_swap12 hcontAt
    have hswap23 :
        iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
          iteratedFDeriv ℝ 3 f x ![u₁, u₃, u₂] :=
      iteratedFDeriv_three_swap23 hdom_open hcont hx u₁ u₂ u₃
    by_cases hu₁ : ‖u₁‖[f; x] = 0
    · -- First discharge the radical cases exactly as in the source proof: if one direction has
      -- zero local norm, factor through the Hessian radical and the trilinear map vanishes.
      have hu₁_ann :
          ∀ z : E, inner ℝ u₁ (hessian f x z) = 0 :=
        (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u₁) hxPos).1 hu₁
      have hzero :
          iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] = 0 :=
        iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
          (dom := dom) (Mf := Mf) (f := f) (x := x) (u := u₁) (v := u₂) (w := u₃)
          hdom_open hcont hx hxPos hdiagAt hu₁_ann
      rw [hzero, hu₁]
      simp
    by_cases hu₂ : ‖u₂‖[f; x] = 0
    · have hu₂_ann :
          ∀ z : E, inner ℝ u₂ (hessian f x z) = 0 :=
        (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u₂) hxPos).1 hu₂
      have hzero_first :
          iteratedFDeriv ℝ 3 f x ![u₂, u₁, u₃] = 0 :=
        iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
          (dom := dom) (Mf := Mf) (f := f) (x := x) (u := u₂) (v := u₁) (w := u₃)
          hdom_open hcont hx hxPos hdiagAt hu₂_ann
      have hzero :
          iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] = 0 := by
        calc
          iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]
              = iteratedFDeriv ℝ 3 f x ![u₂, u₁, u₃] := hswap12
          _ = 0 := hzero_first
      rw [hzero, hu₂]
      simp
    by_cases hu₃ : ‖u₃‖[f; x] = 0
    · have hu₃_ann :
          ∀ z : E, inner ℝ u₃ (hessian f x z) = 0 :=
        (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u₃) hxPos).1 hu₃
      have hzero_first :
          iteratedFDeriv ℝ 3 f x ![u₃, u₁, u₂] = 0 :=
        iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
          (dom := dom) (Mf := Mf) (f := f) (x := x) (u := u₃) (v := u₁) (w := u₂)
          hdom_open hcont hx hxPos hdiagAt hu₃_ann
      have hzero :
          iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] = 0 := by
        calc
          iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]
              = iteratedFDeriv ℝ 3 f x ![u₁, u₃, u₂] := hswap23
          _ = iteratedFDeriv ℝ 3 f x ![u₃, u₁, u₂] :=
            iteratedFDeriv_three_swap12
              (f := f) (x := x) (u₁ := u₁) (u₂ := u₃) (u₃ := u₂) hcontAt
          _ = 0 := hzero_first
      rw [hzero, hu₃]
      simp
    have hdvv :
        ∀ d v : E,
          |iteratedFDeriv ℝ 3 f x ![d, v, v]| ≤
            2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) :=
      iteratedFDeriv_dvv_bound_of_diagonal_bound
        (dom := dom) (Mf := Mf) (f := f) (x := x)
        hdom_open hcont hx hxPos hdiagAt
    -- Route correction: after separating the radical cases, the mixed estimate is now reduced to
    -- the sharp repeated-slot bound plus bilinear polarization in the last two slots.
    exact iteratedFDeriv_mixed_bound_of_dvv_bound
      (dom := dom) (Mf := Mf) (f := f) (x := x)
      (u₁ := u₁) (u₂ := u₂) (u₃ := u₃)
      hdom_open hcont hx hxPos hu₂ hu₃ hdvv
  · intro htrilinear x hx u
    -- Specialize the mixed estimate to the diagonal and rewrite back to the source-facing owner.
    have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
    have hdiag : |iteratedFDeriv ℝ 3 f x ![u, u, u]| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] * ‖u‖[f; x] * ‖u‖[f; x] :=
      htrilinear hx u u u
    rw [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt]
    have hconst : (fun _ : Fin 3 => u) = ![u, u, u] := by
      ext i
      fin_cases i <;> rfl
    simpa [hconst, pow_succ, mul_assoc] using hdiag

namespace IsSelfConcordantOnWith

/-- A self-concordant function satisfies the full trilinear third-derivative estimate on its
domain. -/
theorem iteratedFDeriv_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u₁ u₂ u₃ : E) :
    |iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃]| ≤
      2 * (Mf : ℝ) * ‖u₁‖[f; x] * ‖u₂‖[f; x] * ‖u₃‖[f; x] := by
  have htrilinear :
      ∀ {y : E} (hy : y ∈ dom) (v₁ v₂ v₃ : E),
        |iteratedFDeriv ℝ 3 f y ![v₁, v₂, v₃]| ≤
          2 * (Mf : ℝ) * ‖v₁‖[f; y] * ‖v₂‖[f; y] * ‖v₃‖[f; y] :=
    (selfConcordant_diagonal_bound_iff_trilinear_bound
      hself.isOpen_domain
      hself.contDiffOn
      fun hx' ↦ hself.hessian_isPositive hx').1
      (fun hx' u ↦ hself.third_deriv_bound hx' u)
  exact htrilinear hx u₁ u₂ u₃

end IsSelfConcordantOnWith
