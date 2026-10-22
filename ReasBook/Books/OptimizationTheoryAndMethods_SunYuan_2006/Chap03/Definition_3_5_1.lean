/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Eigenspace.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Mathlib recall: use `gradient` and `fderiv` for the Hessian owner,
-- and `Module.End.HasEigenvalue` for the negative-eigenvalue condition.

/-- The Hessian operator at `x`, represented by `fderiv ℝ (gradient f) x`.
This is the canonical derived operator attached to `gradient`/`fderiv`; Hessian-based
predicates below add the needed regularity hypotheses so this operator is used only at
genuine Hessian points. -/
abbrev hessianAt (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient f) x

/-- The quadratic form associated to `hessianAt f x`. -/
abbrev hessianQuadraticAt (f : E → ℝ) (x d : E) : ℝ :=
  inner ℝ d (hessianAt f x d)

/-- Chapter03 Definition 3.5.1 (1): an indefinite point is a point where the Hessian
has a negative quadratic direction. This keeps the source-facing owner at the quadratic-form
level used by the textbook, while spectral hypotheses remain available through bridge lemmas
below. -/
def IsIndefinitePoint (f : E → ℝ) (x : E) : Prop :=
  ∃ d : E, hessianQuadraticAt f x d < 0

/-- A negative Hessian quadratic direction forces `gradient f` to be differentiable at `x`,
because the totalized fallback `fderiv` off differentiability is `0`, so the quadratic form
vanishes in every direction. -/
theorem IsIndefinitePoint.gradient_differentiableAt {f : E → ℝ} {x : E}
    (h : IsIndefinitePoint f x) :
    DifferentiableAt ℝ (gradient f) x := by
  by_contra hnot
  have hhessian : hessianAt f x = 0 := by
    simp [hessianAt, fderiv_zero_of_not_differentiableAt hnot]
  rcases h with ⟨d, hd⟩
  have hzero : hessianQuadraticAt f x d = 0 := by
    simp [hessianQuadraticAt, hhessian]
  have : ¬ hessianQuadraticAt f x d < 0 := by
    simp [hzero]
  exact this hd

/-- Unfolding lemma for `IsIndefinitePoint`. -/
theorem isIndefinitePoint_iff (f : E → ℝ) (x : E) :
    IsIndefinitePoint f x ↔ ∃ d : E, hessianQuadraticAt f x d < 0 :=
  Iff.rfl

/-- Chapter03 Definition 3.5.1 (2): a negative curvature direction at an indefinite point
is a direction `d` with `hessianQuadraticAt f x d < 0`. -/
def IsNegativeCurvatureDirectionAt (f : E → ℝ) (x d : E) : Prop :=
  hessianQuadraticAt f x d < 0

/-- Unfolding lemma for `IsNegativeCurvatureDirectionAt`. -/
theorem isNegativeCurvatureDirectionAt_iff (f : E → ℝ) (x d : E) :
    IsNegativeCurvatureDirectionAt f x d ↔ hessianQuadraticAt f x d < 0 :=
  Iff.rfl

/-- A negative curvature direction is automatically an indefinite point. -/
theorem IsNegativeCurvatureDirectionAt.isIndefinitePoint {f : E → ℝ} {x d : E}
    (h : IsNegativeCurvatureDirectionAt f x d) :
    IsIndefinitePoint f x :=
  ⟨d, h⟩

/-- An indefinite descent pair uses a negative curvature direction and nonpositive
first-order directional derivatives along both components. -/
class IsIndefiniteDescentPairAt (f : E → ℝ) (x s d : E) : Prop where
  negative_curvature : IsNegativeCurvatureDirectionAt f x d
  inner_left_nonpos : inner ℝ s (gradient f x) ≤ 0
  inner_right_nonpos : inner ℝ d (gradient f x) ≤ 0

/-- The curvature component of an indefinite descent pair is strictly negative. -/
theorem IsIndefiniteDescentPairAt.hessianQuadratic_neg {f : E → ℝ} {x s d : E}
    (h : IsIndefiniteDescentPairAt f x s d) :
    hessianQuadraticAt f x d < 0 := by
  exact h.negative_curvature

/-- A non-indefinite descent pair uses the source branch where `x` is not an indefinite
point, `s` is a strict descent direction, `d` is nonascending, and the Hessian quadratic
form vanishes along `d`. Since `hessianAt` is defined through `fderiv`, the existence of the
Hessian is recorded explicitly here instead of being left to the totalized zero fallback. -/
class IsNonIndefiniteDescentPairAt (f : E → ℝ) (x s d : E) : Prop where
  not_indefinite : ¬IsIndefinitePoint f x
  gradient_differentiableAt : DifferentiableAt ℝ (gradient f) x
  left_descent : IsDescentDirectionAt f x s
  inner_right_nonpos : inner ℝ d (gradient f x) ≤ 0
  hessianQuadratic_eq_zero : hessianQuadraticAt f x d = 0

/-- The strict first-order branch of a non-indefinite descent pair is the Chapter 1
descent-direction owner. -/
theorem IsNonIndefiniteDescentPairAt.inner_left_neg {f : E → ℝ} {x s d : E}
    (h : IsNonIndefiniteDescentPairAt f x s d) :
    inner ℝ s (gradient f x) < 0 := by
  simpa [real_inner_comm] using h.left_descent.inner_gradient_neg

/-- The quadratic form of a Hessian eigenvector is the eigenvalue times the squared norm. -/
theorem hessianQuadraticAt_eq_mul_normSq_of_eigenvector
    {f : E → ℝ} {x u : E} {μ : ℝ} (hu_eigen : hessianAt f x u = μ • u) :
    hessianQuadraticAt f x u = μ * ‖u‖ ^ 2 := by
  calc
    hessianQuadraticAt f x u = inner ℝ u (μ • u) := by simp [hessianQuadraticAt, hu_eigen]
    _ = μ * inner ℝ u u := by rw [inner_smul_right]
    _ = μ * ‖u‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]

/-- A negative Hessian eigenvector gives a negative curvature direction. -/
theorem isNegativeCurvatureDirectionAt_of_negative_eigenvector
    {f : E → ℝ} {x u : E} {μ : ℝ}
    (hμ : μ < 0) (hu_eigen : hessianAt f x u = μ • u) (hu_ne : u ≠ 0) :
    IsNegativeCurvatureDirectionAt f x u := by
  rw [isNegativeCurvatureDirectionAt_iff, hessianQuadraticAt_eq_mul_normSq_of_eigenvector hu_eigen]
  exact mul_neg_of_neg_of_pos hμ (pow_pos (norm_pos_iff.mpr hu_ne) 2)

/-- A negative Hessian eigenvalue makes the point indefinite in the quadratic-form sense. -/
theorem isIndefinitePoint_of_hasNegativeEigenvalue
    {f : E → ℝ} {x : E} {μ : ℝ}
    (hμ : μ < 0) (hμ_eigen : Module.End.HasEigenvalue (hessianAt f x).toLinearMap μ) :
    IsIndefinitePoint f x := by
  rcases hμ_eigen.exists_hasEigenvector with ⟨u, hu⟩
  exact IsNegativeCurvatureDirectionAt.isIndefinitePoint
    (isNegativeCurvatureDirectionAt_of_negative_eigenvector hμ hu.apply_eq_smul hu.2)

/-- The Hessian at `x` is positive semidefinite when its quadratic form is nonnegative in
every direction. This keeps the source-facing owner at the `dᵀ ∇²f(x) d` layer that the
definition uses directly, while requiring `gradient f` to be differentiable at `x` so that
`hessianAt f x` is a genuine Hessian rather than the totalized `fderiv` fallback. -/
def HasPositiveSemidefiniteHessianAt (f : E → ℝ) (x : E) : Prop :=
  DifferentiableAt ℝ (gradient f) x ∧ ∀ d : E, 0 ≤ hessianQuadraticAt f x d

/-- Chapter03 Definition 3.5.1 (3): a descent pair at `x` is given either by the
indefinite-point inequalities or by the non-indefinite-point inequalities in the source. -/
def IsDescentPairAt (f : E → ℝ) (x s d : E) : Prop :=
  IsIndefiniteDescentPairAt f x s d ∨ IsNonIndefiniteDescentPairAt f x s d

/-- Every descent pair has nonpositive first-order pairing along `s`. -/
theorem IsDescentPairAt.inner_left_nonpos {f : E → ℝ} {x s d : E}
    (h : IsDescentPairAt f x s d) :
    inner ℝ s (gradient f x) ≤ 0 := by
  rcases h with h | h
  · exact h.inner_left_nonpos
  · exact le_of_lt h.inner_left_neg

/-- Every descent pair has nonpositive Hessian quadratic term along `d`. -/
theorem IsDescentPairAt.hessianQuadratic_nonpos {f : E → ℝ} {x s d : E}
    (h : IsDescentPairAt f x s d) :
    hessianQuadraticAt f x d ≤ 0 := by
  rcases h with h | h
  · exact le_of_lt h.hessianQuadratic_neg
  · simp [h.hessianQuadratic_eq_zero]

/-- Helper for Chapter03 Definition 3.5.1: a positive-semidefinite Hessian rules out
negative Hessian quadratic directions, hence rules out indefinite points. -/
theorem not_isIndefinitePoint_of_hasPositiveSemidefiniteHessianAt
    {f : E → ℝ} {x : E} (hpsd : HasPositiveSemidefiniteHessianAt f x) :
    ¬ IsIndefinitePoint f x := by
  -- A positive-semidefinite quadratic form cannot take a negative value.
  rintro ⟨d, hd⟩
  exact not_lt_of_ge (hpsd.2 d) hd

/-- Helper for Chapter03 Definition 3.5.1: once the Hessian exists, the absence of
negative quadratic directions is exactly positive semidefiniteness. -/
theorem hasPositiveSemidefiniteHessianAt_of_not_isIndefinitePoint
    {f : E → ℝ} {x : E} (hHessian : DifferentiableAt ℝ (gradient f) x)
    (hnot : ¬ IsIndefinitePoint f x) :
    HasPositiveSemidefiniteHessianAt f x := by
  refine ⟨hHessian, ?_⟩
  intro d
  -- Convert the global non-indefinite hypothesis into a pointwise quadratic inequality.
  exact not_lt.mp (fun hd ↦ hnot ⟨d, hd⟩)

/-- Helper for Chapter03 Definition 3.5.1: the Hessian quadratic form scales by the square
of a real scalar. -/
theorem hessianQuadraticAt_smul {f : E → ℝ} {x d : E} {a : ℝ} :
    hessianQuadraticAt f x (a • d) = a ^ 2 * hessianQuadraticAt f x d := by
  -- Pull the scalar through the linear Hessian map and both inner-product slots.
  calc
    hessianQuadraticAt f x (a • d) = inner ℝ (a • d) (a • hessianAt f x d) := by
      simp [hessianQuadraticAt]
    _ = a * (a * inner ℝ d (hessianAt f x d)) := by
      rw [inner_smul_right, inner_smul_left]
      simp
    _ = a ^ 2 * hessianQuadraticAt f x d := by
      ring_nf

/-- Helper for Chapter03 Definition 3.5.1: negating a direction preserves negative
curvature because the Hessian quadratic form is even. -/
theorem IsNegativeCurvatureDirectionAt.neg {f : E → ℝ} {x d : E}
    (h : IsNegativeCurvatureDirectionAt f x d) :
    IsNegativeCurvatureDirectionAt f x (-d) := by
  -- Rewrite the negated direction as a scalar multiple and use the evenness lemma.
  simpa [isNegativeCurvatureDirectionAt_iff, hessianQuadraticAt_smul]
    using h

/-- Helper for Chapter03 Definition 3.5.1: the negative gradient always has nonpositive
pairing with the gradient itself. -/
theorem inner_neg_gradient_nonpos (f : E → ℝ) (x : E) :
    inner ℝ (-gradient f x) (gradient f x) ≤ 0 := by
  -- Rewrite to the negative of a squared norm.
  rw [inner_neg_left]
  have hself_nonneg : 0 ≤ inner ℝ (gradient f x) (gradient f x) := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_nonneg ‖gradient f x‖
  exact neg_nonpos.mpr hself_nonneg

/-- Helper for Chapter03 Definition 3.5.1: a nonzero gradient makes the negative gradient a
strict descent direction. -/
theorem isDescentDirectionAt_neg_gradient_of_gradient_ne (f : E → ℝ) (x : E)
    (hgrad : gradient f x ≠ 0) :
    IsDescentDirectionAt f x (-gradient f x) := by
  -- The directional derivative along `-gradient f x` is the negative norm square.
  rw [IsDescentDirectionAt, inner_neg_right]
  have hself_pos : 0 < inner ℝ (gradient f x) (gradient f x) := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hgrad) 2
  linarith

/-- Helper for Chapter03 Definition 3.5.1: every indefinite point admits a descent pair by
choosing `s = -gradient f x` and orienting the negative-curvature direction so that its
first-order pairing is nonpositive. -/
theorem exists_descentPairAt_of_isIndefinitePoint {f : E → ℝ} {x : E}
    (h : IsIndefinitePoint f x) :
    ∃ s d : E, IsDescentPairAt f x s d := by
  rcases h with ⟨d, hd⟩
  rcases inner_gradient_nonpos_or_neg_nonpos f x d with hpair | hpair
  · refine ⟨-gradient f x, d, Or.inl ?_⟩
    refine
      { negative_curvature := hd
        inner_left_nonpos := ?_
        inner_right_nonpos := ?_ }
    · -- The steepest-descent choice always has nonpositive first-order pairing.
      exact inner_neg_gradient_nonpos f x
    · -- This is the chosen orientation of the negative-curvature direction.
      simpa [real_inner_comm] using hpair
  · refine ⟨-gradient f x, -d, Or.inl ?_⟩
    refine
      { negative_curvature := (show IsNegativeCurvatureDirectionAt f x d from hd).neg
        inner_left_nonpos := ?_
        inner_right_nonpos := ?_ }
    · -- The same steepest-descent estimate works in the flipped branch.
      exact inner_neg_gradient_nonpos f x
    · -- The sign choice makes the right pairing nonpositive after commuting the inner product.
      simpa [real_inner_comm] using hpair

/-- Chapter03 Definition 3.5.1 (4): in the positive-semidefinite branch of the source
example, if `∇ f x ≠ 0`, then `s = -gradient f x` and `d = 0` form a descent pair. -/
theorem zero_exampleDescentPairAt (f : E → ℝ) (x : E)
    (hpsd : HasPositiveSemidefiniteHessianAt f x) (hgrad : gradient f x ≠ 0) :
    IsDescentPairAt f x (-gradient f x) 0 := by
  -- Use the non-indefinite branch supplied by the positive-semidefinite Hessian.
  refine Or.inr
    { not_indefinite := not_isIndefinitePoint_of_hasPositiveSemidefiniteHessianAt hpsd
      gradient_differentiableAt := hpsd.1
      left_descent := ?_
      inner_right_nonpos := ?_
      hessianQuadratic_eq_zero := ?_ }
  · -- A nonzero gradient makes `-gradient f x` a strict descent direction.
    exact isDescentDirectionAt_neg_gradient_of_gradient_ne f x hgrad
  · -- The zero direction has zero first-order pairing.
    simp
  · -- The zero direction also has zero Hessian quadratic value.
    simp [hessianQuadraticAt]

/-- Chapter03 Definition 3.5.1 (5): in the negative-curvature branch of the source
example, if `u` is an eigenvector for a negative eigenvalue of the Hessian at `x` and
`inner ℝ u (gradient f x) ≠ 0`, then `s = -gradient f x` and
`d = -(Real.sign (inner ℝ u (gradient f x))) • u` form a descent pair. -/
theorem negativeEigenvector_exampleDescentPairAt
    (f : E → ℝ) (x u : E) (μ : ℝ)
    (hμ : μ < 0) (hu_eigen : hessianAt f x u = μ • u)
    (hu_grad : inner ℝ u (gradient f x) ≠ 0) :
    IsDescentPairAt f x (-gradient f x)
      ((-(Real.sign (inner ℝ u (gradient f x)))) • u) := by
  let t := inner ℝ u (gradient f x)
  have ht_ne : t ≠ 0 := hu_grad
  have hu_ne : u ≠ 0 := by
    intro hu0
    exact hu_grad (by simp [hu0])
  have hneg_curv_u : IsNegativeCurvatureDirectionAt f x u :=
    isNegativeCurvatureDirectionAt_of_negative_eigenvector hμ hu_eigen hu_ne
  have hsign_sq : (-(Real.sign t)) ^ 2 = 1 := by
    -- A nonzero real sign is either `-1` or `1`, so its square is `1`.
    rcases Real.sign_apply_eq_of_ne_zero t ht_ne with hsign | hsign <;> simp [hsign]
  refine Or.inl
    { negative_curvature := ?_
      inner_left_nonpos := ?_
      inner_right_nonpos := ?_ }
  · -- Scaling by a unit sign preserves the negative quadratic value.
    rw [isNegativeCurvatureDirectionAt_iff, hessianQuadraticAt_smul, hsign_sq, one_mul]
    simpa [isNegativeCurvatureDirectionAt_iff] using hneg_curv_u
  · -- The left component is again the negative gradient.
    exact inner_neg_gradient_nonpos f x
  · -- The sign choice makes the first-order pairing equal to the negative absolute value.
    have hsign_nonneg : 0 ≤ Real.sign t * t := Real.sign_mul_nonneg t
    calc
      inner ℝ ((-(Real.sign t)) • u) (gradient f x) = -(Real.sign t * t) := by
        simp [t, mul_comm]
      _ ≤ 0 := by
        linarith

/-- Chapter03 Definition 3.5.1 (6): in the orthogonal subcase of the negative-curvature
branch, if `u` is a nonzero eigenvector for a negative eigenvalue of the Hessian at `x`
and `inner ℝ u (gradient f x) = 0`, then both `d = u` and `d = -u` with
`s = -gradient f x` form descent pairs. -/
theorem orthogonalNegativeEigenvector_exampleDescentPairAt
    (f : E → ℝ) (x u : E) (μ : ℝ)
    (hμ : μ < 0) (hu_eigen : hessianAt f x u = μ • u) (hu_ne : u ≠ 0)
    (hu_grad : inner ℝ u (gradient f x) = 0) :
    IsDescentPairAt f x (-gradient f x) u ∧
      IsDescentPairAt f x (-gradient f x) (-u) := by
  have hneg_curv_u : IsNegativeCurvatureDirectionAt f x u :=
    isNegativeCurvatureDirectionAt_of_negative_eigenvector hμ hu_eigen hu_ne
  constructor
  · refine Or.inl
      { negative_curvature := hneg_curv_u
        inner_left_nonpos := ?_
        inner_right_nonpos := ?_ }
    · -- The left component is again the negative gradient.
      exact inner_neg_gradient_nonpos f x
    · -- Orthogonality gives the required nonpositive pairing for `u`.
      simp [hu_grad]
  · refine Or.inl
      { negative_curvature := hneg_curv_u.neg
        inner_left_nonpos := ?_
        inner_right_nonpos := ?_ }
    · -- The left component is again the negative gradient.
      exact inner_neg_gradient_nonpos f x
    · -- Orthogonality is unchanged after negating the direction.
      have hgrad_comm : inner ℝ (gradient f x) u = 0 := by
        simpa [real_inner_comm] using hu_grad
      rw [real_inner_comm, inner_neg_right, hgrad_comm]
      simp

/-- Chapter03 Definition 3.5.1 (7): there is no descent pair at `x` exactly when
`gradient f x = 0` and the Hessian at `x` is positive semidefinite. This equivalence is only
valid at genuine Hessian points, so differentiability of `gradient f` at `x` is an explicit
hypothesis rather than being left implicit in `fderiv`. -/
theorem not_exists_descentPairAt_iff (f : E → ℝ) (x : E)
    (hHessian : DifferentiableAt ℝ (gradient f) x) :
    (¬ ∃ s d : E, IsDescentPairAt f x s d) ↔
      gradient f x = 0 ∧ HasPositiveSemidefiniteHessianAt f x := by
  constructor
  · intro hno
    have hnot_indef : ¬ IsIndefinitePoint f x := by
      -- Any indefinite point would yield a descent pair by the source construction.
      intro hindef
      rcases exists_descentPairAt_of_isIndefinitePoint hindef with ⟨s, d, hsd⟩
      exact hno ⟨s, d, hsd⟩
    have hpsd : HasPositiveSemidefiniteHessianAt f x :=
      hasPositiveSemidefiniteHessianAt_of_not_isIndefinitePoint hHessian hnot_indef
    have hgrad_zero : gradient f x = 0 := by
      by_contra hgrad_ne
      exact hno ⟨-gradient f x, 0, zero_exampleDescentPairAt f x hpsd hgrad_ne⟩
    exact ⟨hgrad_zero, hpsd⟩
  · rintro ⟨hgrad_zero, hpsd⟩ ⟨s, d, hsd⟩
    rcases hsd with hindef | hnonindef
    · -- Positive semidefiniteness rules out the indefinite branch.
      exact (not_isIndefinitePoint_of_hasPositiveSemidefiniteHessianAt hpsd)
        hindef.negative_curvature.isIndefinitePoint
    · -- Vanishing gradient contradicts the strict descent requirement in the non-indefinite branch.
      have : ¬ inner ℝ s (gradient f x) < 0 := by
        simp [hgrad_zero]
      exact this hnonindef.inner_left_neg

end
