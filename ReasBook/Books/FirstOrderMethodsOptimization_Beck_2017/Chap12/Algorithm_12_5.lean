/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_41
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)

noncomputable section

namespace EuclideanSpace

section

variable {ι : Type*} [Fintype ι]

/-- The coordinatewise projection of `s` onto the upper box `{z | z_i ≤ b_i}` in
`EuclideanSpace ℝ ι`. -/
def upperBoxClamp (s b : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i ↦ min (s i) (b i))

end

end EuclideanSpace

section

variable {n p : ℕ}

open EuclideanSpace (upperBoxClamp)

/- Algorithm 12.5 is `source-facing`: it gives the explicit dual projection-gradient recursion for
the polyhedral system `A x ≤ b`.

Domain sampling identifies the abstraction layers as follows.
- `source-facing`: the explicit DPG dual sequence `y^k` and the derived primal points `x^k`;
- `core/canonical`: the Chapter 12.1 admissible stepsize owner
  `DualBasedProximalGradientDualStepsizeParameter` specialized to `σ = 1`, together with the
  Chapter 12.2 trajectory owner `is_dual_proximal_gradient_primal_trajectory`;
- `bridge/view`: the projection-specific explicit formulas `Aᵀ y + d` and
  `y - (1 / L) A x + (1 / L) upperBoxClamp (A x - L y) b` realizing the Chapter 12.2
  argmax/proximal steps for the quadratic projection model.

The primitive projection data are therefore the shared stepsize owner, the pointwise minimum
`upperBoxClamp x b` onto the upper box in `ℝ^p`, the explicit primal point, and the explicit dual
update. The recursive iterate families remain source-facing, while the canonical Chapter 12.2
owner is recovered by a bridge theorem. -/

/-- The admissible constant stepsize parameters for the polyhedral projection problem. This is the
Chapter 12.1 dual stepsize owner specialized to the projection objective, whose strong-convexity
modulus is `σ = 1`. -/
abbrev PolyhedralProjectionStepsizeParameter
    (A : Matrix (Fin p) (Fin n) ℝ) :=
  DualBasedProximalGradientDualStepsizeParameter
    (A.toEuclideanLin.toContinuousLinearMap) 1

-- Proof sketch: specialize the Chapter 12.1 lower-bound theorem at `σ = 1`, then simplify the
-- resulting scalar expression `‖A‖² / 1`.
/-- Every admissible polyhedral-projection stepsize parameter satisfies `‖A‖₂,₂² ≤ L`. -/
theorem polyhedral_projection_stepsize_parameter_lower_bound
    (A : Matrix (Fin p) (Fin n) ℝ) (L : PolyhedralProjectionStepsizeParameter A) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ (2 : ℕ) ≤ (L : ℝ) := by
  -- Specialize the Chapter 12.1 lower bound at `σ = 1` and simplify the denominator.
  simpa [dual_based_proximal_gradient_dual_lipschitz_constant_eq] using
    DualBasedProximalGradientDualStepsizeParameter.lower_bound L

/-- Helper for Algorithm 12.5: if `y ≤ b`, then the residual from clamping `s` above by `b`
has nonpositive product with the feasible displacement from the same clamp to `y`. -/
theorem sub_min_mul_nonpos_of_le_right
    (s y b : ℝ) (hy : y ≤ b) :
    (s - min s b) * (y - min s b) ≤ 0 := by
  -- Split on whether `s` already lies below the upper bound `b`.
  by_cases hs : s ≤ b
  · rw [min_eq_left hs]
    simp
  · have hb : b ≤ s := le_of_not_ge hs
    rw [min_eq_right hb]
    have hs_nonneg : 0 ≤ s - b := sub_nonneg.mpr hb
    have hy_nonpos : y - b ≤ 0 := sub_nonpos.mpr hy
    exact mul_nonpos_of_nonneg_of_nonpos hs_nonneg hy_nonpos

/-- The shared primal point `Aᵀ y + d` attached to the current dual iterate `y`. -/
def polyhedral_projection_primal_point
    (A : Matrix (Fin p) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin n) :=
  A.transpose.toEuclideanLin y + d

/-- The shared explicit dual update from a primal point `x` and current dual point `y`:
`y - (1 / L) A x + (1 / L) upperBoxClamp (A x - L y) b`. -/
def polyhedral_projection_dual_update
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p))
    (L : PosReal) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  y - (1 / L : ℝ) • A.toEuclideanLin x +
    (1 / L : ℝ) • upperBoxClamp (A.toEuclideanLin x - (L : ℝ) • y) b

/-- Algorithm 12.5: given `A`, `b`, `d`, an admissible constant parameter `L ≥ ‖A‖₂,₂²`, and an
initial dual point `y⁰ = y0`, the polyhedral projection DPG method generates the dual iterates
`y^k` by recursively applying the shared primal-point and dual-update formulas. -/
def polyhedral_projection_dpg_dual_iterates
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A)
    (y0 : EuclideanSpace ℝ (Fin p)) :
    ℕ → EuclideanSpace ℝ (Fin p)
  | 0 => y0
  | k + 1 =>
      let yk := polyhedral_projection_dpg_dual_iterates A b d L y0 k
      polyhedral_projection_dual_update A b L
        (polyhedral_projection_primal_point A d yk) yk

/-- The associated primal iterates `x^k = Aᵀ y^k + d` derived from the DPG dual recursion. -/
def polyhedral_projection_dpg_primal_iterates
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A)
    (y0 : EuclideanSpace ℝ (Fin p)) :
    ℕ → EuclideanSpace ℝ (Fin n) :=
  fun k ↦ polyhedral_projection_primal_point A d
    (polyhedral_projection_dpg_dual_iterates A b d L y0 k)

section

variable
    (A : Matrix (Fin p) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
variable (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p))

/-- The polyhedral projection DPG dual sequence starts from the prescribed initialization
`y⁰ = y0`. -/
theorem polyhedral_projection_dpg_dual_iterates_zero
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) :
    polyhedral_projection_dpg_dual_iterates A b d L y0 0 = y0 := by
  -- The recursion is initialized at the prescribed point `y0`.
  rfl

-- Proof sketch: unfold `polyhedral_projection_dpg_dual_iterates` at `k + 1`; the recursive
-- clause applies the shared dual-update owner to the current iterate `y^k`.
/-- Each successor dual iterate is obtained by evaluating the shared dual update at the current
dual iterate and its associated primal point. -/
theorem polyhedral_projection_dpg_dual_iterates_succ
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    polyhedral_projection_dpg_dual_iterates A b d L y0 (k + 1) =
      polyhedral_projection_dual_update A b L
        (polyhedral_projection_primal_point A d
          (polyhedral_projection_dpg_dual_iterates A b d L y0 k))
        (polyhedral_projection_dpg_dual_iterates A b d L y0 k) := by
  -- Unfold the recursive successor clause once.
  rfl

-- Proof sketch: unfold `polyhedral_projection_dpg_primal_iterates`; by definition `x^k` is the
-- shared primal-point owner evaluated at the current dual iterate `y^k`.
/-- The primal iterates satisfy the textbook identity `x^k = Aᵀ y^k + d`. -/
theorem polyhedral_projection_dpg_primal_iterates_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    polyhedral_projection_dpg_primal_iterates A b d L y0 k =
      A.transpose.toEuclideanLin
          (polyhedral_projection_dpg_dual_iterates A b d L y0 k) + d := by
  -- The primal iterate is defined by applying the shared primal-point formula.
  rfl

/-- Helper for Algorithm 12.5: splitting the affine term at the explicit primal point `Aᵀ y + d`
separates the residual inner product from the constant contributions. -/
theorem polyhedral_projection_primal_point_inner_split
    (A : Matrix (Fin p) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p))
    (x' : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x' (A.transpose.toEuclideanLin y) =
      inner ℝ (A.transpose.toEuclideanLin y)
        (x' - polyhedral_projection_primal_point A d y) +
      inner ℝ d (A.transpose.toEuclideanLin y) +
      ‖A.transpose.toEuclideanLin y‖ ^ (2 : ℕ) := by
  let xBar := polyhedral_projection_primal_point A d y
  let a := A.transpose.toEuclideanLin y
  have hxBar : xBar = a + d := by
    change polyhedral_projection_primal_point A d y = A.transpose.toEuclideanLin y + d
    rfl
  -- Split the affine term at the translated point `xBar = Aᵀ y + d`, then expand the inner
  -- product of `xBar` with `Aᵀ y` into its self and data components.
  calc
    inner ℝ x' (A.transpose.toEuclideanLin y)
        = inner ℝ ((x' - xBar : EuclideanSpace ℝ (Fin n)) + xBar) a := by
            congr 1
            abel
    _ = inner ℝ (x' - xBar) a + inner ℝ xBar a := by
      rw [inner_add_left]
    _ = inner ℝ a (x' - xBar) + inner ℝ xBar a := by
      rw [real_inner_comm]
    _ = inner ℝ a (x' - xBar) +
          (inner ℝ a a + inner ℝ d a) := by
      rw [hxBar, inner_add_left]
    _ = inner ℝ a (x' - xBar) +
          (‖a‖ ^ (2 : ℕ) + inner ℝ d a) := by
      rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ a (x' - xBar) + inner ℝ d a + ‖a‖ ^ (2 : ℕ) := by
      ring
    _ = inner ℝ (A.transpose.toEuclideanLin y)
          (x' - polyhedral_projection_primal_point A d y) +
        inner ℝ d (A.transpose.toEuclideanLin y) +
        ‖A.transpose.toEuclideanLin y‖ ^ (2 : ℕ) := by
      rfl

/-- Helper for Algorithm 12.5: subtracting the datum `d` from the explicit primal point
`polyhedral_projection_primal_point A d y` recovers the affine term `Aᵀ y`. -/
theorem polyhedral_projection_primal_point_sub_data
    (A : Matrix (Fin p) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    polyhedral_projection_primal_point A d y - d = A.transpose.toEuclideanLin y := by
  -- Expand the explicit primal point and cancel the translated datum.
  ext i
  simp [polyhedral_projection_primal_point]

/-- Helper for Algorithm 12.5: the affine-minus-quadratic step-(a) objective is a constant minus
the squared distance to the explicit primal point `Aᵀ y + d`. -/
theorem polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq_real
    (A : Matrix (Fin p) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p))
    (x' : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x' (A.transpose.toEuclideanLin y) -
        (1 / 2 : ℝ) * ‖(x' - d : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖polyhedral_projection_primal_point A d y‖ ^ (2 : ℕ) -
        (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) -
        (1 / 2 : ℝ) *
          ‖x' - polyhedral_projection_primal_point A d y‖ ^ (2 : ℕ) := by
  let xBar := polyhedral_projection_primal_point A d y
  have hbar : xBar - d = A.transpose.toEuclideanLin y := by
    -- Reuse the explicit primal-point normal form while keeping the proof at the `xBar` center.
    simpa [xBar, polyhedral_projection_primal_point] using
      add_sub_cancel (A.transpose.toEuclideanLin y) d
  have hsplit :
      inner ℝ x' (A.transpose.toEuclideanLin y) =
        inner ℝ (A.transpose.toEuclideanLin y) (x' - xBar) +
          inner ℝ d (A.transpose.toEuclideanLin y) +
          ‖A.transpose.toEuclideanLin y‖ ^ (2 : ℕ) := by
    -- Rewrite the mixed term in the normal form centered at `xBar`.
    simpa [xBar] using
      polyhedral_projection_primal_point_inner_split (A := A) (d := d) y x'
  have hquad :
      (1 / 2 : ℝ) * ‖(x' - d : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖A.transpose.toEuclideanLin y‖ ^ (2 : ℕ) +
          inner ℝ (A.transpose.toEuclideanLin y) (x' - xBar) +
          (1 / 2 : ℝ) * ‖(x' - xBar : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) := by
    -- Translate the quadratic penalty from `d` to the center `xBar`.
    simpa [xBar, polyhedral_projection_primal_point] using
      quadratic_translate_identity d xBar x'
  have hconst :
      (1 / 2 : ℝ) * ‖xBar‖ ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) +
          inner ℝ d (A.transpose.toEuclideanLin y) +
          (1 / 2 : ℝ) * ‖A.transpose.toEuclideanLin y‖ ^ (2 : ℕ) := by
    -- The constant term is the same translation identity evaluated at the center.
    simpa [xBar, polyhedral_projection_primal_point] using
      quadratic_translate_identity (0 : EuclideanSpace ℝ (Fin n)) d xBar
  -- Route correction: close the completed square from the two explicit normal-form bridges above.
  nlinarith [hsplit, hquad, hconst]

/-- Helper for Algorithm 12.5: the affine-minus-quadratic step-(a) objective is a constant minus
the squared distance to the explicit primal point `Aᵀ y + d`. -/
theorem polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq
    (A : Matrix (Fin p) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p))
    (x' : EuclideanSpace ℝ (Fin n)) :
    ((inner ℝ x' (A.transpose.toEuclideanLin y) : EReal) -
      denoising_data_fidelity d x') =
      (((1 / 2 : ℝ) * ‖polyhedral_projection_primal_point A d y‖ ^ (2 : ℕ) -
          (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) -
          (1 / 2 : ℝ) *
            ‖x' - polyhedral_projection_primal_point A d y‖ ^ (2 : ℕ) : ℝ) :
        EReal) := by
  have hhalf :
      (‖(x' - d : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) / 2 : ℝ) =
        (1 / 2 : ℝ) * ‖(x' - d : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) := by
    ring
  -- Convert the EReal-valued objective to the real completed-square identity and coerce back.
  rw [denoising_data_fidelity_apply, hhalf, EReal.coe_sub]
  exact congrArg
    (fun t : ℝ ↦ (t : EReal))
    (polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq_real
      (A := A) (d := d) y x')

/-- Private helper for Algorithm 12.5: the explicit primal point `Aᵀ y + d` globally maximizes
the step-(a) affine-minus-quadratic objective. -/
private theorem polyhedral_projection_primal_point_isMaxOn
    (A : Matrix (Fin p) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    IsMaxOn
      (fun x' : EuclideanSpace ℝ (Fin n) ↦
        ((inner ℝ x' (A.toEuclideanLin.adjoint y) : EReal) -
          denoising_data_fidelity d x'))
      Set.univ
      (polyhedral_projection_primal_point A d y) := by
  let xBar := polyhedral_projection_primal_point A d y
  -- Rewrite the adjoint once into the stable transpose normal form used by the completed square.
  have hadj : A.toEuclideanLin.adjoint y = A.transpose.toEuclideanLin y := by
    have hlin : A.toEuclideanLin.adjoint = A.transpose.toEuclideanLin := by
      simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
    simpa using
      congrArg
        (fun T : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) ↦ T y)
        hlin
  -- Route correction: use `isMaxOn_univ_iff` instead of manually expanding filter/set syntax.
  rw [isMaxOn_univ_iff]
  intro x'
  have hxObjective :
      ((inner ℝ x' (A.toEuclideanLin.adjoint y) : EReal) -
          denoising_data_fidelity d x') =
        (((1 / 2 : ℝ) * ‖xBar‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖(x' - xBar : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    -- Rewrite the objective at `x'` into the constant-minus-square normal form.
    simpa [xBar, hadj] using
      (polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq
        (A := A) (d := d) y x')
  have hcenterObjective :
      ((inner ℝ xBar (A.toEuclideanLin.adjoint y) : EReal) -
          denoising_data_fidelity d xBar) =
        (((1 / 2 : ℝ) * ‖xBar‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    -- At the center `xBar`, the residual squared norm vanishes.
    simpa [xBar, hadj] using
      (polyhedral_projection_affine_minus_quadratic_eq_constant_sub_sq
        (A := A) (d := d) y xBar)
  have hresidualNonneg : 0 ≤ (1 / 2 : ℝ) * ‖(x' - xBar : EuclideanSpace ℝ (Fin n))‖ ^ (2 : ℕ) := by
    positivity
  -- Compare the centered formulas; maximality is exactly nonnegativity of the residual square.
  rw [hxObjective, hcenterObjective]
  exact EReal.coe_le_coe_iff.mpr (by nlinarith)

/-- The explicit primal point `Aᵀ y + d` is the Chapter 12.2 step-(a) argmax point for the
quadratic projection objective. -/
theorem polyhedral_projection_primal_point_mem_argmax
    (A : Matrix (Fin p) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    polyhedral_projection_primal_point A d y ∈
      dual_proximal_gradient_primal_x_argmax
        (denoising_data_fidelity d) A.toEuclideanLin y := by
  -- Unfold the Chapter 12 argmax owner and reuse the centered maximality theorem.
  rw [mem_dual_proximal_gradient_primal_x_argmax_iff]
  simpa using polyhedral_projection_primal_point_isMaxOn (A := A) (d := d) y

/-- Helper for Algorithm 12.5: the upper box `{z | z_i ≤ b_i}` is convex. -/
theorem polyhedral_projection_upper_box_convex
    (b : EuclideanSpace ℝ (Fin p)) :
    Convex ℝ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i} := by
  -- Check the convex inequality coordinatewise against the common upper bound `b`.
  intro x hx y hy a c ha hc hac i
  calc
    (a • x + c • y) i = a * x i + c * y i := by simp
    _ ≤ a * b i + c * b i := by
      gcongr
      · exact hx i
      · exact hy i
    _ = b i := by
      calc
        a * b i + c * b i = (a + c) * b i := by ring
        _ = b i := by rw [hac, one_mul]

/-- Helper for Algorithm 12.5: `upperBoxClamp s b` is the projection of `s` onto the upper box
`{z | z_i ≤ b_i}`. -/
theorem upperBoxClamp_mem_projection_mapping_upper_box
    (s : EuclideanSpace ℝ (Fin p)) :
    upperBoxClamp s b ∈
      P[{z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}] s := by
  -- Use the Chapter 6 variational characterization of projections onto convex sets.
  have hclamp_mem :
      upperBoxClamp s b ∈ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i} := by
    intro i
    simpa [EuclideanSpace.upperBoxClamp] using (min_le_right (s i) (b i))
  refine
    (mem_projection_mapping_iff_inner_le_zero
      {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}
      (polyhedral_projection_upper_box_convex (b := b))
      s hclamp_mem).2 ?_
  intro y hy
  -- Rewrite the Euclidean inner product as a finite sum of coordinatewise scalar products.
  have hcoord :
      ∀ i : Fin p,
        inner ℝ (s i - upperBoxClamp s b i) (y i - upperBoxClamp s b i) ≤ 0 := by
    intro i
    have hmul :
        (s i - min (s i) (b i)) * (y i - min (s i) (b i)) ≤ 0 :=
      sub_min_mul_nonpos_of_le_right (s i) (y i) (b i) (hy i)
    have hinner :
        inner ℝ (s i - upperBoxClamp s b i) (y i - upperBoxClamp s b i) =
          (s i - min (s i) (b i)) * (y i - min (s i) (b i)) := by
      simpa [EuclideanSpace.upperBoxClamp] using
        (RCLike.inner_apply'
          (s i - min (s i) (b i))
          (y i - min (s i) (b i)) :
          inner ℝ (s i - min (s i) (b i)) (y i - min (s i) (b i)) =
            (s i - min (s i) (b i)) * (y i - min (s i) (b i)))
    rw [hinner]
    exact hmul
  calc
    inner ℝ (s - upperBoxClamp s b) (y - upperBoxClamp s b)
        = ∑ i : Fin p,
            inner ℝ (s i - upperBoxClamp s b i) (y i - upperBoxClamp s b i) := by
            simp [PiLp.inner_apply]
    _ ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro i hi
      exact hcoord i

/-- Helper for Algorithm 12.5: positive scaling does not change the indicator of the upper box
`{z : EuclideanSpace ℝ (Fin p) | ∀ i, z i ≤ b i}`. -/
theorem polyhedral_projection_smul_extendedIndicator_upper_box_eq :
    (((L : EReal) • δ_ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}) :
      EuclideanSpace ℝ (Fin p) → EReal) =
      δ_ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i} := by
  -- The indicator takes only the values `0` and `⊤`, and positive scaling fixes both of them.
  funext z
  by_cases hz : z ∈ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}
  · simp [extendedIndicator, hz, Pi.smul_apply, smul_eq_mul]
  · simp [extendedIndicator, hz, Pi.smul_apply, smul_eq_mul,
      EReal.coe_mul_top_of_pos (L : PosReal).2]

/-- Helper for Algorithm 12.5: the clipped point `upperBoxClamp (A x - L y) b` is a proximal
point of the scaled upper-box indicator at `A x - L y`. -/
theorem polyhedral_projection_clipped_point_mem_scaled_indicator_prox
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    upperBoxClamp (A.toEuclideanLin x - (L : ℝ) • y) b ∈
      prox (((L : EReal) • δ_ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}))
        (A.toEuclideanLin x - (L : ℝ) • y) := by
  -- Reduce the scaled indicator to the unscaled indicator, then use projection membership.
  have hbox_nonempty :
      ({z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i} :
        Set (EuclideanSpace ℝ (Fin p))).Nonempty := by
    refine ⟨b, ?_⟩
    intro i
    show (b i : ℝ) ≤ b i
    exact le_rfl
  have hproj :
      upperBoxClamp (A.toEuclideanLin x - (L : ℝ) • y) b ∈
        P[{z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}]
          (A.toEuclideanLin x - (L : ℝ) • y) := by
    simpa using
      upperBoxClamp_mem_projection_mapping_upper_box
        (b := b)
        (A.toEuclideanLin x - (L : ℝ) • y)
  have hproxMem :
      upperBoxClamp (A.toEuclideanLin x - (L : ℝ) • y) b ∈
        prox[extendedIndicator {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}]
          (A.toEuclideanLin x - (L : ℝ) • y) := by
    rw [prox_extendedIndicator_eq_projection_mapping
      {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i} hbox_nonempty]
    exact hproj
  rw [polyhedral_projection_smul_extendedIndicator_upper_box_eq (b := b) (L := L)]
  simpa using hproxMem

/-- The explicit clipped dual update realizes the Chapter 12.2 step-(b) primal proximal update
for the indicator of the upper box `{z | z ≤ b}`. -/
theorem polyhedral_projection_dual_update_mem_y_step
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin p)) :
    polyhedral_projection_dual_update A b L x y ∈
      dual_proximal_gradient_primal_y_step
        (δ_ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}) A.toEuclideanLin x y L := by
  -- Package the explicit clipped point as the witness required by the Chapter 12 step owner.
  rw [mem_dual_proximal_gradient_primal_y_step_iff]
  refine ⟨upperBoxClamp (A.toEuclideanLin x - (L : ℝ) • y) b, ?_, ?_⟩
  · exact polyhedral_projection_clipped_point_mem_scaled_indicator_prox
      (A := A) (b := b) (L := L) x y
  · simp [polyhedral_projection_dual_update]

-- Proof sketch: combine `polyhedral_projection_dpg_dual_iterates_succ` with
-- the explicit dual-update definition, then rewrite the primal point through
-- `polyhedral_projection_dpg_primal_iterates_eq`.
/-- The dual iterates satisfy the textbook general step
`y^(k+1) = y^k - (1 / L) A x^k + (1 / L) upperBoxClamp (A x^k - L y^k) b`. -/
theorem polyhedral_projection_dpg_dual_iterates_update
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    polyhedral_projection_dpg_dual_iterates A b d L y0 (k + 1) =
      polyhedral_projection_dpg_dual_iterates A b d L y0 k -
        (1 / L : ℝ) • A.toEuclideanLin (polyhedral_projection_dpg_primal_iterates A b d L y0 k) +
        (1 / L : ℝ) •
          upperBoxClamp
            (A.toEuclideanLin (polyhedral_projection_dpg_primal_iterates A b d L y0 k) -
              (L : ℝ) • polyhedral_projection_dpg_dual_iterates A b d L y0 k)
            b := by
  -- Unfold the successor iterate and rewrite the shared primal point as `x^k`.
  rw [polyhedral_projection_dpg_dual_iterates_succ, polyhedral_projection_dpg_primal_iterates_eq]
  rfl

/-- Each primal iterate `x^k` lies in the Chapter 12.2 primal argmax set determined by the
current dual iterate `y^k`. -/
theorem polyhedral_projection_dpg_primal_iterates_mem_argmax
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    polyhedral_projection_dpg_primal_iterates A b d L y0 k ∈
      dual_proximal_gradient_primal_x_argmax
        (denoising_data_fidelity d) A.toEuclideanLin
        (polyhedral_projection_dpg_dual_iterates A b d L y0 k) := by
  -- Rewrite `x^k` to the explicit primal point and reuse the pointwise argmax proof.
  simpa [polyhedral_projection_dpg_primal_iterates_eq] using
    polyhedral_projection_primal_point_mem_argmax
      (A := A) (d := d)
      (polyhedral_projection_dpg_dual_iterates A b d L y0 k)

/-- Each successor dual iterate belongs to the Chapter 12.2 primal proximal-update set based at
the current pair `(x^k, y^k)`. -/
theorem polyhedral_projection_dpg_dual_iterates_mem_y_step
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    polyhedral_projection_dpg_dual_iterates A b d L y0 (k + 1) ∈
      dual_proximal_gradient_primal_y_step
        (δ_ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i}) A.toEuclideanLin
        (polyhedral_projection_dpg_primal_iterates A b d L y0 k)
        (polyhedral_projection_dpg_dual_iterates A b d L y0 k) L := by
  -- Rewrite the successor iterate to the explicit dual-update owner and reuse the step-(b) proof.
  rw [polyhedral_projection_dpg_dual_iterates_succ]
  simpa [polyhedral_projection_dpg_primal_iterates_eq] using
    polyhedral_projection_dual_update_mem_y_step
      (A := A) (b := b) (L := L)
      (polyhedral_projection_dpg_primal_iterates A b d L y0 k)
      (polyhedral_projection_dpg_dual_iterates A b d L y0 k)

/-- The explicit polyhedral projection recursion is a Chapter 12.2 dual proximal-gradient primal
trajectory for the quadratic objective and the upper-box indicator. -/
theorem polyhedral_projection_dpg_is_dual_proximal_gradient_primal_trajectory
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin p)) (d : EuclideanSpace ℝ (Fin n))
    (L : PolyhedralProjectionStepsizeParameter A) (y0 : EuclideanSpace ℝ (Fin p)) :
    is_dual_proximal_gradient_primal_trajectory
      (denoising_data_fidelity d)
      (δ_ {z : EuclideanSpace ℝ (Fin p) | ∀ i : Fin p, z i ≤ b i})
      A.toEuclideanLin
      L
      y0
      (polyhedral_projection_dpg_primal_iterates A b d L y0)
      (polyhedral_projection_dpg_dual_iterates A b d L y0) := by
  -- Assemble the initialization, step-(a), and step-(b) owner theorems.
  refine ⟨?_, ?_, ?_⟩
  · exact polyhedral_projection_dpg_dual_iterates_zero A b d L y0
  · intro k
    exact polyhedral_projection_dpg_primal_iterates_mem_argmax A b d L y0 k
  · intro k
    exact polyhedral_projection_dpg_dual_iterates_mem_y_step A b d L y0 k

end

end
