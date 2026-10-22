/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable [∀ i, CompleteSpace (E i)]

/- Theorem 11.8 is a `bridge/view` result from the Chapter 11 block-gradient surface to the
Chapter 5 smoothness owner `is_l_smooth_on`.

Domain sampling for this refinement:
- `is_l_smooth_on` from `Chap05/Definition_5_1` is the owner smoothness predicate.
- `block_partial_gradient`, notation `∇[i] φ`, from `Chap11/Definition_11_3` is the canonical
  block-gradient owner on `PiLp 2 E`.
- `𝒰[i]`, also from `Chap11/Definition_11_3`, is the canonical block insertion map.

The primitive data here are only the convex differentiable function `φ` and the block Lipschitz
constants `Li`. The block partial gradient itself is already a derived owner-level notion in
Chapter 11, so it should not remain a parallel primitive parameter of this theorem. The theorem
surface only needs a finite block index type and the Hilbert-space structure required to form
`∇`; finite-dimensionality belongs, at most, to one possible Chapter 5 proof route, not to the
mathematical statement. -/

-- Proof sketch: first identify the gradient of each frozen one-block slice
-- `d ↦ φ (x + 𝒰[i] d)` with the canonical block partial gradient `∇[i] φ`. Then transport the
-- given block Lipschitz hypothesis to show those slices are `Li i`-smooth on `Set.univ`. Finally,
-- use the convex auxiliary function from the textbook proof to turn these one-block estimates into
-- a global gradient bound. The current frontier below has already stabilized the slice calculus
-- and the convex supporting-plane inequality; only the zero-`L_i` auxiliary-function branch
-- remains to be finished.

omit [∀ i, CompleteSpace (E i)] in
/-- Helper for Theorem 11.8: composing the ambient dual functional with the `i`-th block insertion
recovers the dual functional induced by the `i`-th coordinate. -/
lemma toDual_comp_block_single_eq_block_toDual
    [DecidableEq ι] (i : ι) (v : PiLp (2 : ENNReal) E) :
    (InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) v).comp
        (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.single ℝ E i)) =
      InnerProductSpace.toDualMap ℝ (E i) (v i) := by
  ext d
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDualMap_apply_apply]
  change inner ℝ v (WithLp.toLp (2 : ENNReal) (Pi.single i d)) = inner ℝ (v i) d
  rw [PiLp.toLp_single, PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Helper for Theorem 11.8: the frozen `i`-th block slice `d ↦ φ(x + 𝒰[i] d)` has gradient equal
to the `i`-th block partial gradient of `φ` at the translated point. -/
lemma block_slice_hasGradientAt
    (φ : PiLp (2 : ENNReal) E → ℝ)
    (hφ_diff : Differentiable ℝ φ)
    (i : ι) (x : PiLp (2 : ENNReal) E) (d : E i) :
    HasGradientAt
      (fun e : E i ↦ φ (x + 𝒰[i] e))
      ((∇[i] φ) (x + 𝒰[i] d))
      d := by
  classical
  rw [hasGradientAt_iff_hasFDerivAt]
  let L : E i →L[ℝ] PiLp (2 : ENNReal) E :=
    ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.single ℝ E i)
  -- Differentiate the affine block-insertion map `e ↦ x + 𝒰[i] e`.
  have hL :
      HasFDerivAt (fun e : E i ↦ x + 𝒰[i] e) L d := by
    simpa [L] using
      (L.hasFDerivAt.const_add x : HasFDerivAt (fun e : E i ↦ x + L e) L d)
  -- Compose the derivative of `φ` with that block-insertion derivative.
  have hφ' :
      HasFDerivAt φ
        (InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) (∇ φ (x + 𝒰[i] d)))
        (x + 𝒰[i] d) := by
    simpa using (hφ_diff (x + 𝒰[i] d)).hasGradientAt.hasFDerivAt
  have hcomp := hφ'.comp d hL
  rw [show
      (InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) (∇ φ (x + 𝒰[i] d))).comp L =
        InnerProductSpace.toDualMap ℝ (E i) ((∇[i] φ) (x + 𝒰[i] d)) by
      simpa [L, block_partial_gradient_eq_gradient] using
        toDual_comp_block_single_eq_block_toDual
          (E := E) (i := i) (v := ∇ φ (x + 𝒰[i] d))] at hcomp
  simpa using hcomp

/-- Helper for Theorem 11.8: every frozen one-block slice inherits the corresponding smoothness
constant from the block partial-gradient Lipschitz hypothesis. -/
lemma block_slice_is_l_smooth_on
    (φ : PiLp (2 : ENNReal) E → ℝ)
    (Li : ι → NNReal)
    (hφ_diff : Differentiable ℝ φ)
    (h_block_partial_gradient_lipschitz :
      ∀ (i : ι) (x : PiLp (2 : ENNReal) E) (d : E i),
        ‖(∇[i] φ) x - (∇[i] φ) (x + 𝒰[i] d)‖ ≤
          (Li i : ℝ) * ‖d‖)
    (i : ι) (x : PiLp (2 : ENNReal) E) :
    is_l_smooth_on (fun d : E i ↦ φ (x + 𝒰[i] d)) Set.univ (Li i) := by
  classical
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro d _
    exact (block_slice_hasGradientAt (E := E) φ hφ_diff i x d).differentiableAt
  · intro d _ e _
    have hrewrite :
        (x + 𝒰[i] d) + 𝒰[i] (e - d) = x + 𝒰[i] e := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [sub_eq_add_neg, add_left_comm, add_comm]
      · simp [hji]
    -- Recenter the block-Lipschitz hypothesis at the slice point `x + 𝒰[i] d`.
    have hblock :=
      h_block_partial_gradient_lipschitz i (x + 𝒰[i] d) (e - d)
    have hdgrad :
        ∇ (fun u : E i ↦ φ (x + 𝒰[i] u)) d =
          (∇[i] φ) (x + 𝒰[i] d) :=
      (block_slice_hasGradientAt (E := E) φ hφ_diff i x d).gradient
    have hegrad :
        ∇ (fun u : E i ↦ φ (x + 𝒰[i] u)) e =
          (∇[i] φ) (x + 𝒰[i] e) :=
      (block_slice_hasGradientAt (E := E) φ hφ_diff i x e).gradient
    simpa [hdgrad, hegrad, hrewrite, norm_sub_rev] using hblock

/-- Helper for Theorem 11.8: convexity gives the supporting-hyperplane inequality
`φ x ≥ φ y + ⟪∇ φ y, x - y⟫`. -/
lemma convex_supporting_plane_nonnegative
    (φ : PiLp (2 : ENNReal) E → ℝ)
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : Differentiable ℝ φ)
    (x y : PiLp (2 : ENNReal) E) :
    0 ≤ φ x - φ y - inner ℝ (∇ φ y) (x - y) := by
  let line : ℝ →ᵃ[ℝ] PiLp (2 : ENNReal) E := AffineMap.lineMap y x
  let g : ℝ → ℝ := fun t ↦ φ (line t)
  -- Restrict the convex function to the segment joining `y` and `x`.
  have hg_convex : ConvexOn ℝ Set.univ g := by
    simpa [g, line] using hφ_convex.comp_affineMap line
  have hg_deriv : HasDerivAt g (inner ℝ (∇ φ y) (x - y)) 0 := by
    have hφ' :
        HasFDerivAt φ
          (InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) (∇ φ y))
          y := by
      simpa using (hφ_diff y).hasGradientAt.hasFDerivAt
    have hφ'' :
        HasFDerivAt φ
          (InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) (∇ φ y))
          (line 0) := by
      simpa [line] using hφ'
    have hline : HasDerivAt line (x - y) 0 := by
      simpa [line] using
        (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := (0 : ℝ)))
    have hcomp := HasFDerivAt.comp_hasDerivAt (x := 0) hφ'' hline
    simpa [g, line, AffineMap.lineMap_apply_zero] using hcomp
  have hslope :=
    ConvexOn.le_slope_of_hasDerivAt (S := Set.univ) (f := g) hg_convex
      (by simp)
      (by simp)
      (show (0 : ℝ) < 1 by norm_num)
      hg_deriv
  simpa [g, line, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope

/-- Helper for Theorem 11.8: a globally nonnegative function that is `0`-smooth on the whole
space has vanishing gradient everywhere. -/
lemma zero_smooth_nonnegative_gradient_eq_zero
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ψ : H → ℝ)
    (hψ_smooth : is_l_smooth_on ψ Set.univ 0)
    (hψ_nonneg : ∀ z : H, 0 ≤ ψ z)
    (x : H) :
    ∇ ψ x = 0 := by
  by_contra hgrad_ne
  have hnorm_sq_pos : 0 < ‖∇ ψ x‖ ^ (2 : ℕ) := by
    -- The contradiction branch only starts when the gradient norm is strictly positive.
    have hnorm_pos : 0 < ‖∇ ψ x‖ := norm_pos_iff.mpr hgrad_ne
    nlinarith
  have hnorm_sq_ne : ‖∇ ψ x‖ ^ (2 : ℕ) ≠ 0 := by
    exact hnorm_sq_pos.ne'
  let t : ℝ := (ψ x + 1) / ‖∇ ψ x‖ ^ (2 : ℕ)
  have hx_mem : x ∈ (Set.univ : Set H) := by
    simp
  have hy_mem : x - t • ∇ ψ x ∈ (Set.univ : Set H) := by
    simp
  -- Apply the `L = 0` descent lemma at the trial point `x - t • ∇ ψ x`.
  have hdescent :=
    is_l_smooth_on_descent_lemma
      (L := (0 : NNReal))
      (D := Set.univ)
      (f := ψ)
      convex_univ
      hψ_smooth
      hx_mem
      hy_mem
  have hupper :
      ψ (x - t • ∇ ψ x) ≤ ψ x - t * ‖∇ ψ x‖ ^ (2 : ℕ) := by
    -- The quadratic term disappears because the smoothness constant is zero.
    simpa [t, sub_eq_add_neg, inner_smul_right, real_inner_self_eq_norm_sq] using hdescent
  have hmul :
      t * ‖∇ ψ x‖ ^ (2 : ℕ) = ψ x + 1 := by
    -- The chosen step cancels the positive denominator exactly.
    dsimp [t]
    field_simp [hnorm_sq_ne]
  have hneg :
      ψ (x - t • ∇ ψ x) ≤ -1 := by
    rw [hmul] at hupper
    linarith
  have hnonneg :
      0 ≤ ψ (x - t • ∇ ψ x) := hψ_nonneg (x - t • ∇ ψ x)
  linarith

/-- Helper for Theorem 11.8: a globally nonnegative block-smooth function satisfies the
per-block squared gradient estimate from the source proof. -/
lemma nonnegative_block_partial_gradient_sq_le_two_mul_Li_mul_value
    (f : PiLp (2 : ENNReal) E → ℝ)
    (Li : ι → NNReal)
    (hf_diff : Differentiable ℝ f)
    (hf_nonneg : ∀ z : PiLp (2 : ENNReal) E, 0 ≤ f z)
    (h_block_partial_gradient_lipschitz :
      ∀ (i : ι) (x : PiLp (2 : ENNReal) E) (d : E i),
        ‖(∇[i] f) x - (∇[i] f) (x + 𝒰[i] d)‖ ≤
          (Li i : ℝ) * ‖d‖)
    (i : ι) (x : PiLp (2 : ENNReal) E) :
    ‖(∇[i] f) x‖ ^ (2 : ℕ) ≤ 2 * (Li i : ℝ) * f x := by
  by_cases hLi0 : Li i = 0
  · let slice : E i → ℝ := fun d ↦ f (x + 𝒰[i] d)
    have hslice_smooth : is_l_smooth_on slice Set.univ 0 := by
      -- Freeze all blocks except `i` and transport the `L_i = 0` hypothesis to the slice.
      simpa [slice, hLi0] using
        block_slice_is_l_smooth_on
          (E := E)
          f
          Li
          hf_diff
          h_block_partial_gradient_lipschitz
          i
          x
    have hslice_nonneg : ∀ d : E i, 0 ≤ slice d := by
      intro d
      exact hf_nonneg (x + 𝒰[i] d)
    have hslice_grad_zero : ∇ slice 0 = 0 := by
      exact zero_smooth_nonnegative_gradient_eq_zero slice hslice_smooth hslice_nonneg 0
    have hslice_grad :
        ∇ slice 0 = (∇[i] f) x := by
      -- At `d = 0`, the slice gradient is exactly the block partial gradient at `x`.
      have hslice_grad0 :=
        (block_slice_hasGradientAt (E := E) f hf_diff i x (0 : E i)).gradient
      have hzero_update : x + 𝒰[i] (0 : E i) = x := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [show (∇[i] f) (x + 𝒰[i] (0 : E i)) = (∇[i] f) x by rw [hzero_update]] at hslice_grad0
      simpa [slice] using hslice_grad0
    have hblock_zero : (∇[i] f) x = 0 := by
      rw [← hslice_grad]
      exact hslice_grad_zero
    -- The zero-smooth branch collapses both sides to zero.
    simp [hLi0, hblock_zero]
  · let slice : E i → ℝ := fun d ↦ f (x + 𝒰[i] d)
    let step : E i := -((1 / (Li i : ℝ)) • (∇[i] f) x)
    have hLi_pos : 0 < (Li i : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hLi0)
    have hstep_mem : step ∈ (Set.univ : Set (E i)) := by
      simp
    have hzero_mem : (0 : E i) ∈ (Set.univ : Set (E i)) := by
      simp
    have hslice_smooth : is_l_smooth_on slice Set.univ (Li i) := by
      -- The positive branch uses the standard one-step descent on the frozen block slice.
      simpa [slice] using
        block_slice_is_l_smooth_on
          (E := E)
          f
          Li
          hf_diff
          h_block_partial_gradient_lipschitz
          i
          x
    have hdescent :=
      is_l_smooth_on_descent_lemma
        (L := Li i)
        (D := Set.univ)
        (f := slice)
        convex_univ
        hslice_smooth
        hzero_mem
        hstep_mem
    have hslice_nonneg : 0 ≤ slice step := by
      exact hf_nonneg (x + 𝒰[i] step)
    have hslice_grad :
        ∇ slice 0 = (∇[i] f) x := by
      -- Identify the linear term in the descent lemma with the block partial gradient.
      have hslice_grad0 :=
        (block_slice_hasGradientAt (E := E) f hf_diff i x (0 : E i)).gradient
      have hzero_update : x + 𝒰[i] (0 : E i) = x := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [show (∇[i] f) (x + 𝒰[i] (0 : E i)) = (∇[i] f) x by rw [hzero_update]] at hslice_grad0
      simpa [slice] using hslice_grad0
    have hzero_update : x + 𝒰[i] (0 : E i) = x := by
      ext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    have hdescent' :
        f (x + 𝒰[i] step) ≤
          f x - (1 / (Li i : ℝ)) * ‖(∇[i] f) x‖ ^ (2 : ℕ) +
            ((Li i : ℝ) / 2) * (((1 / (Li i : ℝ)) * ‖(∇[i] f) x‖) ^ (2 : ℕ)) := by
      -- Simplify the descent bound at the textbook step `-(1 / L_i) ∇_i f(x)`.
      simpa [slice, step, hslice_grad, hzero_update, sub_eq_add_neg, inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, norm_neg,
        abs_of_nonneg (le_of_lt (one_div_pos.mpr hLi_pos))] using hdescent
    have hquadratic :
        f x - (1 / (Li i : ℝ)) * ‖(∇[i] f) x‖ ^ (2 : ℕ) +
            ((Li i : ℝ) / 2) * (((1 / (Li i : ℝ)) * ‖(∇[i] f) x‖) ^ (2 : ℕ)) =
          f x - (1 / (2 * (Li i : ℝ))) * ‖(∇[i] f) x‖ ^ (2 : ℕ) := by
      field_simp [hLi_pos.ne']
      ring
    have hdescent'' :
        f (x + 𝒰[i] step) ≤
          f x - (1 / (2 * (Li i : ℝ))) * ‖(∇[i] f) x‖ ^ (2 : ℕ) := by
      rw [hquadratic] at hdescent'
      exact hdescent'
    have hcore :
        (1 / (2 * (Li i : ℝ))) * ‖(∇[i] f) x‖ ^ (2 : ℕ) ≤ f x := by
      -- Combine the descent estimate with nonnegativity of the slice value at the trial point.
      have hslice_nonneg' : 0 ≤ f (x + 𝒰[i] step) := hslice_nonneg
      linarith
    -- Multiply the lower bound by `2L_i` to reach the denominator-free form.
    have hmul :
        (2 * (Li i : ℝ)) *
            ((1 / (2 * (Li i : ℝ))) * ‖(∇[i] f) x‖ ^ (2 : ℕ)) ≤
          (2 * (Li i : ℝ)) * f x := by
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    have hleft :
        (2 * (Li i : ℝ)) *
            ((1 / (2 * (Li i : ℝ))) * ‖(∇[i] f) x‖ ^ (2 : ℕ)) =
          ‖(∇[i] f) x‖ ^ (2 : ℕ) := by
      field_simp [hLi_pos.ne']
    calc
      ‖(∇[i] f) x‖ ^ (2 : ℕ) =
          (2 * (Li i : ℝ)) *
            ((1 / (2 * (Li i : ℝ))) * ‖(∇[i] f) x‖ ^ (2 : ℕ)) := by
              rw [hleft]
      _ ≤ (2 * (Li i : ℝ)) * f x := hmul

/-- Helper for Theorem 11.8: the textbook auxiliary function satisfies the global squared
gradient bound obtained by summing the per-block estimates. -/
lemma auxiliary_function_gradient_norm_sq_le_two_mul_sum_Li_mul_value
    (φ : PiLp (2 : ENNReal) E → ℝ)
    (Li : ι → NNReal)
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : Differentiable ℝ φ)
    (h_block_partial_gradient_lipschitz :
      ∀ (i : ι) (x : PiLp (2 : ENNReal) E) (d : E i),
        ‖(∇[i] φ) x - (∇[i] φ) (x + 𝒰[i] d)‖ ≤
          (Li i : ℝ) * ‖d‖)
    (x y : PiLp (2 : ENNReal) E) :
    ‖∇ φ x - ∇ φ y‖ ^ (2 : ℕ) ≤
      2 * (((∑ i, Li i : NNReal) : ℝ)) *
        (φ x - φ y - inner ℝ (∇ φ y) (x - y)) := by
  let aux : PiLp (2 : ENNReal) E → ℝ :=
    fun z ↦ φ z - φ y - inner ℝ (∇ φ y) (z - y)
  have haux_diff : Differentiable ℝ aux := by
    -- The auxiliary function is `φ` minus an affine correction.
    have hlin_diff :
        Differentiable ℝ (fun z : PiLp (2 : ENNReal) E ↦ inner ℝ (∇ φ y) (z - y)) := by
      intro z
      have hsub' :
          HasFDerivAt
            (fun w : PiLp (2 : ENNReal) E ↦ w - y)
            (ContinuousLinearMap.id ℝ (PiLp (2 : ENNReal) E))
            z := by
        simpa using (hasFDerivAt_id z).sub_const y
      have hlin' :=
        ((InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) (∇ φ y)).hasFDerivAt.comp z hsub')
      exact hlin'.differentiableAt
    simpa [aux] using (hφ_diff.sub_const (φ y)).sub hlin_diff
  have haux_grad :
      ∀ z : PiLp (2 : ENNReal) E, ∇ aux z = ∇ φ z - ∇ φ y := by
    intro z
    have hφ' :
        HasGradientAt φ (∇ φ z) z := (hφ_diff z).hasGradientAt
    have hsub' :
        HasFDerivAt
          (fun w : PiLp (2 : ENNReal) E ↦ w - y)
          (ContinuousLinearMap.id ℝ (PiLp (2 : ENNReal) E))
          z := by
      simpa using (hasFDerivAt_id z).sub_const y
    have hlin' :
        HasGradientAt
          (fun w : PiLp (2 : ENNReal) E ↦ inner ℝ (∇ φ y) (w - y))
          (∇ φ y)
          z := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa using
        ((InnerProductSpace.toDualMap ℝ (PiLp (2 : ENNReal) E) (∇ φ y)).hasFDerivAt.comp z hsub')
    have haux' :
        HasGradientAt aux (∇ φ z - ∇ φ y) z := by
      -- Differentiate `φ`, subtract the constant `φ y`, then subtract the affine term.
      rw [hasGradientAt_iff_hasFDerivAt] at hφ' hlin' ⊢
      simpa [aux, map_sub] using (hφ'.sub_const (φ y)).sub hlin'
    exact haux'.gradient
  have haux_nonneg :
      ∀ z : PiLp (2 : ENNReal) E, 0 ≤ aux z := by
    intro z
    simpa [aux] using convex_supporting_plane_nonnegative φ hφ_convex hφ_diff z y
  have haux_block_partial_gradient_lipschitz :
      ∀ (i : ι) (z : PiLp (2 : ENNReal) E) (d : E i),
        ‖(∇[i] aux) z - (∇[i] aux) (z + 𝒰[i] d)‖ ≤
          (Li i : ℝ) * ‖d‖ := by
    intro i z d
    have hz :
        (∇[i] aux) z = (∇[i] φ) z - (∇ φ y) i := by
      rw [block_partial_gradient_eq_gradient, haux_grad]
      rfl
    have hzd :
        (∇[i] aux) (z + 𝒰[i] d) =
          (∇[i] φ) (z + 𝒰[i] d) - (∇ φ y) i := by
      rw [block_partial_gradient_eq_gradient, haux_grad]
      rfl
    -- The affine correction cancels in the block-gradient difference.
    simpa [hz, hzd, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      h_block_partial_gradient_lipschitz i z d
  have hblock :
      ∀ i : ι,
        ‖(∇[i] aux) x‖ ^ (2 : ℕ) ≤
          2 * (Li i : ℝ) * aux x := by
    intro i
    -- Apply the generic nonnegative block estimate to the auxiliary function.
    exact
      nonnegative_block_partial_gradient_sq_le_two_mul_Li_mul_value
        (E := E)
        aux
        Li
        haux_diff
        haux_nonneg
        haux_block_partial_gradient_lipschitz
        i
        x
  have hsum :
      ∑ i, ‖(∇[i] aux) x‖ ^ (2 : ℕ) ≤
        ∑ i, 2 * (Li i : ℝ) * aux x := by
    exact Finset.sum_le_sum (fun i _ ↦ hblock i)
  have hleft :
      ∑ i, ‖(∇[i] aux) x‖ ^ (2 : ℕ) =
        ‖∇ φ x - ∇ φ y‖ ^ (2 : ℕ) := by
    -- Rewrite the sum of block norms as the ambient product norm square.
    have hnorm_aux :
        ‖∇ aux x‖ ^ (2 : ℕ) = ∑ i, ‖(∇ aux x) i‖ ^ (2 : ℕ) := by
      simpa using (PiLp.norm_sq_eq_of_L2 (fun i ↦ E i) (∇ aux x))
    calc
      ∑ i, ‖(∇[i] aux) x‖ ^ (2 : ℕ) = ∑ i, ‖(∇ aux x) i‖ ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [block_partial_gradient_eq_gradient]
      _ = ‖∇ aux x‖ ^ (2 : ℕ) := by
        rw [← hnorm_aux]
      _ = ‖∇ φ x - ∇ φ y‖ ^ (2 : ℕ) := by
        rw [haux_grad]
  have hright :
      ∑ i, 2 * (Li i : ℝ) * aux x =
        2 * (((∑ i, Li i : NNReal) : ℝ)) * aux x := by
    -- Factor the common auxiliary value out of the block sum.
    calc
      ∑ i, 2 * (Li i : ℝ) * aux x =
          ∑ i, (2 * aux x) * (Li i : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (2 * aux x) * ∑ i, (Li i : ℝ) := by
        rw [Finset.mul_sum]
      _ = (2 * aux x) * (((∑ i, Li i : NNReal) : ℝ)) := by
        simp [NNReal.coe_sum]
      _ = 2 * (((∑ i, Li i : NNReal) : ℝ)) * aux x := by
        ring
  -- The summed block estimate is the auxiliary-function invariant used by the source proof.
  rw [hleft, hright] at hsum
  simpa [aux] using hsum

/-- Helper for Theorem 11.8: the auxiliary-function squared bound in both orders yields the
global Lipschitz estimate for the gradient. -/
lemma gradient_norm_sub_le_sum_Li_mul_norm_sub
    (φ : PiLp (2 : ENNReal) E → ℝ)
    (Li : ι → NNReal)
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : Differentiable ℝ φ)
    (h_block_partial_gradient_lipschitz :
      ∀ (i : ι) (x : PiLp (2 : ENNReal) E) (d : E i),
        ‖(∇[i] φ) x - (∇[i] φ) (x + 𝒰[i] d)‖ ≤
          (Li i : ℝ) * ‖d‖)
    (x y : PiLp (2 : ENNReal) E) :
    ‖∇ φ x - ∇ φ y‖ ≤
      (((∑ i, Li i : NNReal) : ℝ)) * ‖x - y‖ := by
  let S : ℝ := ((∑ i, Li i : NNReal) : ℝ)
  let dG : PiLp (2 : ENNReal) E := ∇ φ x - ∇ φ y
  have hxy :=
    auxiliary_function_gradient_norm_sq_le_two_mul_sum_Li_mul_value
      (E := E)
      φ
      Li
      hφ_convex
      hφ_diff
      h_block_partial_gradient_lipschitz
      x
      y
  have hyx :=
    auxiliary_function_gradient_norm_sq_le_two_mul_sum_Li_mul_value
      (E := E)
      φ
      Li
      hφ_convex
      hφ_diff
      h_block_partial_gradient_lipschitz
      y
      x
  have haux_sum :
      (φ x - φ y - inner ℝ (∇ φ y) (x - y)) +
        (φ y - φ x - inner ℝ (∇ φ x) (y - x)) =
        inner ℝ dG (x - y) := by
    have hyx_eq : y - x = -(x - y) := by
      abel
    -- Adding the two auxiliary values leaves exactly the gradient difference pairing.
    rw [hyx_eq, inner_neg_right, inner_sub_left]
    ring
  have hsum :
      2 * ‖dG‖ ^ (2 : ℕ) ≤
        2 * S * inner ℝ dG (x - y) := by
    -- Apply the auxiliary estimate in both orders before using Cauchy--Schwarz.
    have hadd := add_le_add hxy hyx
    have hright :
        2 * (((∑ i, Li i : NNReal) : ℝ)) *
            (φ x - φ y - inner ℝ (∇ φ y) (x - y)) +
          2 * (((∑ i, Li i : NNReal) : ℝ)) *
            (φ y - φ x - inner ℝ (∇ φ x) (y - x)) =
          2 * S * inner ℝ dG (x - y) := by
      calc
        2 * (((∑ i, Li i : NNReal) : ℝ)) *
              (φ x - φ y - inner ℝ (∇ φ y) (x - y)) +
            2 * (((∑ i, Li i : NNReal) : ℝ)) *
              (φ y - φ x - inner ℝ (∇ φ x) (y - x)) =
            2 * (((∑ i, Li i : NNReal) : ℝ)) * inner ℝ dG (x - y) := by
              rw [← mul_add, haux_sum]
        _ = 2 * S * inner ℝ dG (x - y) := by
              rfl
    have hleft :
        ‖∇ φ x - ∇ φ y‖ ^ (2 : ℕ) + ‖∇ φ y - ∇ φ x‖ ^ (2 : ℕ) =
          2 * ‖dG‖ ^ (2 : ℕ) := by
      dsimp [dG]
      rw [norm_sub_rev]
      ring
    rw [hleft, hright] at hadd
    exact hadd
  have hsq :
      ‖dG‖ ^ (2 : ℕ) ≤ S * inner ℝ dG (x - y) := by
    nlinarith
  have hS_nonneg : 0 ≤ S := by
    exact_mod_cast (show 0 ≤ ∑ i, Li i from Finset.sum_nonneg fun i _ ↦ NNReal.coe_nonneg _)
  have hcs :
      inner ℝ dG (x - y) ≤ ‖dG‖ * ‖x - y‖ := by
    exact real_inner_le_norm dG (x - y)
  have hsq' :
      ‖dG‖ ^ (2 : ℕ) ≤ S * (‖dG‖ * ‖x - y‖) := by
    exact le_trans hsq (mul_le_mul_of_nonneg_left hcs hS_nonneg)
  by_cases hdG_zero : dG = 0
  · -- The degenerate case is immediate.
    have hzero_rhs : 0 ≤ S * ‖x - y‖ := by
      exact mul_nonneg hS_nonneg (norm_nonneg _)
    have hS_def : S = (((∑ i, Li i : NNReal) : ℝ)) := rfl
    rw [hS_def] at hzero_rhs
    simpa [dG, hdG_zero] using hzero_rhs
  · have hdG_pos : 0 < ‖dG‖ := norm_pos_iff.mpr hdG_zero
    -- Divide the squared inequality by the positive norm `‖dG‖`.
    have hfinal : ‖dG‖ ≤ S * ‖x - y‖ := by
      nlinarith
    simpa [dG, S] using hfinal

/-- Theorem 11.8: if a convex differentiable function on a finite block product `∏ i, E_i` has
canonical block partial gradients `∇ᵢ φ` that are `L_i`-Lipschitz along the `i`-th block
direction `𝒰ᵢ(d)`, then `φ` is globally `L`-smooth with `L = ∑ i, L_i`. -/
theorem convex_block_partial_gradients_lipschitz_is_l_smooth_on
    (φ : PiLp (2 : ENNReal) E → ℝ)
    (Li : ι → NNReal)
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : Differentiable ℝ φ)
    (h_block_partial_gradient_lipschitz :
      ∀ (i : ι) (x : PiLp (2 : ENNReal) E) (d : E i),
        ‖(∇[i] φ) x - (∇[i] φ) (x + 𝒰[i] d)‖ ≤
          (Li i : ℝ) * ‖d‖) :
    is_l_smooth_on φ Set.univ (∑ i, Li i) := by
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Global differentiability is already one of the hypotheses.
    exact hφ_diff x
  · intro x hx y hy
    -- The auxiliary-function argument yields the global gradient Lipschitz estimate.
    exact
      gradient_norm_sub_le_sum_Li_mul_norm_sub
        (E := E)
        φ
        Li
        hφ_convex
        hφ_diff
        h_block_partial_gradient_lipschitz
        x
        y

end
