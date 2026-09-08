module

public import ReasLib.Analysis.StandardQuadratic
public import ReasLib.Optimization.BFGS.Trajectory
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Support

public section

universe u

open scoped Pointwise

namespace BFGS

namespace Scale

/-- The objective obtained by dilating space by `c` and objective values by `c ^ 2`. -/
noncomputable def objective {E : Type u} [SMul ℝ E] (c : ℝ) (F : E → ℝ) (z : E) : ℝ :=
  c ^ 2 * F (c⁻¹ • z)

/-- A quadratically scaled objective evaluates at the inverse-scaled argument. -/
theorem objective_apply {E : Type u} [SMul ℝ E] (c : ℝ) (F : E → ℝ) (z : E) :
    objective c F z = c ^ 2 * F (c⁻¹ • z) := by
  -- Unfolding exposes the inverse dilation followed by quadratic value scaling.
  rfl

/-- Scalar dilation of the argument and quadratic scaling of values preserve
differentiability. -/
theorem objective_differentiable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) {F : E → ℝ} (hF : Differentiable ℝ F) :
    Differentiable ℝ (objective c F) := by
  -- Compose with the continuous scalar dilation and then scale the real output.
  unfold objective
  fun_prop

/-- Scalar dilation of the argument and quadratic scaling of values preserve
continuous differentiability. -/
theorem objective_contDiff {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : WithTop ℕ∞} (c : ℝ) {F : E → ℝ} (hF : ContDiff ℝ m F) :
    ContDiff ℝ m (objective c F) := by
  -- Both scalar dilations are continuously differentiable at every order.
  unfold objective
  fun_prop

/-- Quadratic objective scaling by a nonzero scalar preserves strong convexity on the
whole space with the same modulus. -/
theorem strongConvexOn_objective {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c m : ℝ} (hc : c ≠ 0) {F : E → ℝ}
    (hF : StrongConvexOn Set.univ m F) :
    StrongConvexOn Set.univ m (objective c F) := by
  -- Apply the original strong-convexity inequality to the inverse-scaled endpoints.
  rw [StrongConvexOn, UniformConvexOn] at hF ⊢
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hbase := hF.2 (Set.mem_univ (c⁻¹ • x)) (Set.mem_univ (c⁻¹ • y)) ha hb hab
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  have hnorm : c ^ 2 * ‖c⁻¹ • x - c⁻¹ • y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, pow_two, pow_two]
    field_simp [abs_ne_zero.mpr hc]
    rw [sq_abs]
  -- The spatial and value scalings cancel in the quadratic modulus term.
  calc
    objective c F (a • x + b • y) =
        c ^ 2 * F (a • (c⁻¹ • x) + b • (c⁻¹ • y)) := by
      rw [objective_apply, smul_add, smul_smul, smul_smul]
      congr 2
      module
    _ ≤ c ^ 2 * (a • F (c⁻¹ • x) + b • F (c⁻¹ • y) -
        a * b * (m / 2 * ‖c⁻¹ • x - c⁻¹ • y‖ ^ 2)) := hscaled
    _ = a • objective c F x + b • objective c F y -
        a * b * (m / 2 * ‖x - y‖ ^ 2) := by
      simp only [objective_apply, smul_eq_mul]
      calc
        c ^ 2 * (a * F (c⁻¹ • x) + b * F (c⁻¹ • y) -
            a * b * (m / 2 * ‖c⁻¹ • x - c⁻¹ • y‖ ^ 2)) =
            a * (c ^ 2 * F (c⁻¹ • x)) + b * (c ^ 2 * F (c⁻¹ • y)) -
              a * b * (m / 2 * (c ^ 2 *
                ‖c⁻¹ • x - c⁻¹ • y‖ ^ 2)) := by ring
        _ = a * (c ^ 2 * F (c⁻¹ • x)) + b * (c ^ 2 * F (c⁻¹ • y)) -
              a * b * (m / 2 * ‖x - y‖ ^ 2) := by rw [hnorm]

/-- On a complete real inner-product space, quadratic objective scaling multiplies
the gradient by the spatial scale. -/
theorem gradient_objective_of_completeSpace {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {c : ℝ} (hc : c ≠ 0)
    {F : E → ℝ} (hF : Differentiable ℝ F) (z : E) :
    gradient (objective c F) z = c • gradient F (c⁻¹ • z) := by
  -- First normalize the derivative before transporting it through the Riesz equivalence.
  have hobjective : objective c F = c ^ 2 • (fun w ↦ F (c⁻¹ • w)) := by
    rfl
  have hinner : DifferentiableAt ℝ (fun w ↦ F (c⁻¹ • w)) z := by
    fun_prop
  have hderiv : fderiv ℝ (objective c F) z =
      c • fderiv ℝ F (c⁻¹ • z) := by
    rw [hobjective, fderiv_const_smul hinner, fderiv_comp_smul, smul_smul]
    congr 1
    field_simp
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa only [toDual_gradient, map_smul] using hderiv

/-- The gradient of a nontrivially scaled objective is the correspondingly scaled
gradient at the inverse-scaled point. -/
theorem gradient_objective {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Differentiable ℝ F)
    (z : EuclideanSpace ℝ (Fin n)) :
    gradient (objective c F) z = c • gradient F (c⁻¹ • z) := by
  -- Specialize the Hilbert-space scaling identity to the finite Euclidean space.
  exact gradient_objective_of_completeSpace hc hF z

/-- The derivative of the scaled objective's gradient corresponds to the original
Hessian linear map at the inverse-scaled point. -/
theorem hessian_objective {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiff ℝ 2 F)
    (z : EuclideanSpace ℝ (Fin n)) :
    (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (gradient (objective c F)) z) =
      (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (gradient F) (c⁻¹ • z)) := by
  -- The preceding gradient formula gives a function equality suitable for differentiation.
  have hgradient : gradient (objective c F) =
      fun w ↦ c • gradient F (c⁻¹ • w) := by
    funext w
    have hTwoNeZero : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
    exact gradient_objective_of_completeSpace hc (hF.differentiable hTwoNeZero) w
  -- Differentiate that normalized identity before applying the matrix equivalence.
  have hderiv : fderiv ℝ (gradient (objective c F)) z =
      fderiv ℝ (gradient F) (c⁻¹ • z) := by
    rw [hgradient]
    have hscaled : (fun w ↦ c • gradient F (c⁻¹ • w)) =
        c • (fun w ↦ gradient F (c⁻¹ • w)) := by
      rfl
    rw [hscaled, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact congrArg
    (fun L ↦ (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm L) hderiv

/-- Subtracting the standard quadratic from a scaled objective commutes with
quadratic value scaling and inverse dilation. -/
theorem objective_sub_standardQuadratic_apply {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c : ℝ} (hc : c ≠ 0) (F : E → ℝ) (z : E) :
    (objective c F - (standardQuadratic : E → ℝ)) z =
      c ^ 2 * (F - (standardQuadratic : E → ℝ)) (c⁻¹ • z) := by
  -- Expand only the two computation interfaces, leaving a scalar norm identity.
  simp only [Pi.sub_apply, objective_apply, standardQuadratic_apply, norm_smul,
    Real.norm_eq_abs, norm_inv]
  -- The square removes the absolute value, and the nonzero scale clears its inverse.
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  field_simp [habs]
  rw [sq_abs]
  ring

/-- Scalar dilation carries the topological support of an objective's difference
from the standard quadratic onto the support of the scaled difference. -/
theorem tsupport_sub_quadratic {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c : ℝ} (hc : c ≠ 0) (F : E → ℝ) :
    _root_.tsupport (objective c F - standardQuadratic) =
      c • _root_.tsupport (F - standardQuadratic) := by
  -- Package the pointwise quadratic identity as output scaling after inverse dilation.
  have hscaled : objective c F - standardQuadratic =
      (fun r : ℝ ↦ c ^ 2 * r) ∘
        ((F - (standardQuadratic : E → ℝ)) ∘
          (Homeomorph.smulOfNeZero c hc).symm) := by
    funext z
    rw [Function.comp_apply, Function.comp_apply,
      Homeomorph.smulOfNeZero_symm_apply]
    exact objective_sub_standardQuadratic_apply hc F z
  calc
    _ = _root_.tsupport
        ((F - (standardQuadratic : E → ℝ)) ∘
          (Homeomorph.smulOfNeZero c hc).symm) := by
      rw [hscaled]
      apply tsupport_comp_eq
      intro r
      simp [hc]
    -- A homeomorphic inverse dilation pulls support back to scalar dilation of the set.
    _ = ((Homeomorph.smulOfNeZero c hc).symm) ⁻¹'
        _root_.tsupport (F - standardQuadratic) :=
      tsupport_comp_eq_preimage (F - standardQuadratic)
        (Homeomorph.smulOfNeZero c hc).symm
    _ = c • _root_.tsupport (F - standardQuadratic) := by
      simpa only [Homeomorph.smulOfNeZero_symm_apply] using
        Set.preimage_smul_inv₀ hc (_root_.tsupport (F - standardQuadratic))

end Scale

variable {ι : Type u} [Fintype ι]

/-- Scaling the gradient by a real scalar scales the associated BFGS search
direction by the same scalar. -/
theorem searchDirection_smul [DecidableEq ι]
    (B : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) (c : ℝ) :
    searchDirection B (c • g) = c • searchDirection B g := by
  -- Route correction: use the owner's computation theorem because the imported
  -- definition is opaque here, then move the scalar through each linear operation.
  simp only [searchDirection_def, map_smul, Matrix.mulVec_smul]
  rw [← smul_neg, map_smul]

/-- Simultaneously scaling both secant vectors by a nonzero scalar leaves the BFGS
rank-two update unchanged. -/
theorem update_smul {c : ℝ} (hc : c ≠ 0) (B : Matrix ι ι ℝ)
    (s y : EuclideanSpace ℝ ι) :
    update B (c • s) (c • y) = update B s y := by
  -- Bilinearity contributes the same factor `c ^ 2` to each denominator and numerator.
  classical
  have hquadratic : dotProduct (c • s.ofLp) (Matrix.mulVec B (c • s.ofLp)) =
      c ^ 2 * dotProduct s.ofLp (Matrix.mulVec B s.ofLp) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hsecant : dotProduct (c • s.ofLp) (c • y.ofLp) =
      c ^ 2 * dotProduct s.ofLp y.ofLp := by
    rw [smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hstepRank : Matrix.vecMulVec (c • s.ofLp) (c • s.ofLp) =
      c ^ 2 • Matrix.vecMulVec s.ofLp s.ofLp := by
    rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
    congr 1
    ring
  have hgradientRank : Matrix.vecMulVec (c • y.ofLp) (c • y.ofLp) =
      c ^ 2 • Matrix.vecMulVec y.ofLp y.ofLp := by
    rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
    congr 1
    ring
  have hcancel (a : ℝ) (M : Matrix ι ι ℝ) :
      (c ^ 2 * a)⁻¹ • (c ^ 2 • M) = a⁻¹ • M := by
    rw [mul_inv_rev, smul_smul, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hc), mul_one]
  rw [update_def, update_def]
  simp only [WithLp.ofLp_smul]
  -- Inverting the scalar product cancels that nonzero quadratic factor independently
  -- of whether either secant denominator itself vanishes.
  rw [hquadratic, hsecant, hstepRank, hgradientRank, Matrix.mul_smul,
    Matrix.smul_mul, hcancel, hcancel]

end BFGS

namespace LineSearch.IsExact

/-- Quadratic scaling of objective values and scalar dilation of both the base point
and direction preserve a selected exact line-search parameter. -/
theorem quadraticScale {E : Type u} [AddCommGroup E] [Module ℝ E]
    {F : E → ℝ} {x d : E} {α c : ℝ} (h : LineSearch.IsExact F x d α) (hc : c ≠ 0) :
    LineSearch.IsExact (BFGS.Scale.objective c F) (c • x) (c • d) α := by
  -- Exactness separates into feasibility and minimization on the nonnegative ray.
  rw [LineSearch.isExact_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  have hline : (fun t : ℝ ↦
      BFGS.Scale.objective c F (c • x + t • (c • d))) =
      (fun r : ℝ ↦ c ^ 2 * r) ∘ (fun t : ℝ ↦ F (x + t • d)) := by
    funext t
    rw [BFGS.Scale.objective_apply]
    congr 1
    simp [smul_add, smul_smul, hc, mul_comm]
  -- Multiplication by `c ^ 2` is monotone, so it preserves the selected minimizer.
  have hmono : Monotone (fun r : ℝ ↦ c ^ 2 * r) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab (sq_nonneg c)
  have hmin := h.2.comp_mono hmono
  rw [← hline] at hmin
  exact hmin

end LineSearch.IsExact

namespace BFGS

namespace IsTrajectory

/-- A nonzero scalar dilation transports an exact-line-search BFGS trajectory while
retaining its Hessian matrices and selected step sizes. -/
theorem scale {ι : Type u} [Fintype ι] [DecidableEq ι]
    {F : EuclideanSpace ℝ ι → ℝ} {B₀ : Matrix ι ι ℝ}
    {x : ℕ → EuclideanSpace ℝ ι} {B : ℕ → Matrix ι ι ℝ} {α : ℕ → ℝ}
    (hRun : IsTrajectory F B₀ x B α) {c : ℝ} (hc : c ≠ 0) :
    IsTrajectory (Scale.objective c F) B₀ (fun k ↦ c • x k) B α := by
  -- Expose the six trajectory laws once, preserving the initial matrix and positivity verbatim.
  rw [isTrajectory_iff] at hRun ⊢
  rcases hRun with ⟨hInitial, hDifferentiable, hPosDef, hExact, hStep, hUpdate⟩
  refine ⟨hInitial, Scale.objective_differentiable c hDifferentiable, hPosDef, ?_, ?_, ?_⟩
  · intro k
    -- The scaled gradient and search direction each contribute the same factor `c`.
    simpa only [Scale.gradient_objective_of_completeSpace hc hDifferentiable,
      inv_smul_smul₀ hc,
      searchDirection_smul] using (hExact k).quadraticScale hc
  · intro k
    -- Scalar multiplication transports the original iterate recurrence term by term.
    rw [Scale.gradient_objective_of_completeSpace hc hDifferentiable, inv_smul_smul₀ hc,
      searchDirection_smul]
    simpa only [smul_add, smul_smul, mul_comm] using
      congrArg (fun z ↦ c • z) (hStep k)
  · intro k
    -- Both secant vectors are scalar multiples, so update homogeneity restores `B (k + 1)`.
    rw [Scale.gradient_objective_of_completeSpace hc hDifferentiable,
      inv_smul_smul₀ hc, Scale.gradient_objective_of_completeSpace hc hDifferentiable,
      inv_smul_smul₀ hc]
    simp only [← smul_sub, update_smul hc]
    exact hUpdate k

end IsTrajectory

end BFGS
