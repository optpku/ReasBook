module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import ReasLib.LinearAlgebra.EuclideanSpace.OrthogonalSum

public section

noncomputable section

universe u v

namespace EuclideanSpace.OrthogonalSum.Gradient

/-- The continuous linear projection onto the left coordinates of a Euclidean orthogonal
sum. -/
def left {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] :
    EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] EuclideanSpace ℝ ι :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ)).comp
    (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := κ)).toContinuousLinearMap

/-- The continuous linear projection onto the right coordinates of a Euclidean orthogonal
sum. -/
def right {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] :
    EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] EuclideanSpace ℝ κ :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ)).comp
    (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := κ)).toContinuousLinearMap

/-- The left projection of a vector reconstructed from orthogonal-sum coordinates is its
left coordinate. -/
@[simp]
theorem left_sumEquivProd_symm {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    left ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (x, y)) = x := by
  simp [left]

/-- The right projection of a vector reconstructed from orthogonal-sum coordinates is its
right coordinate. -/
@[simp]
theorem right_sumEquivProd_symm {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    right ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (x, y)) = y := by
  simp [right]

/-- The inner product on a Euclidean orthogonal sum is the sum of the inner products of
its two coordinate projections. -/
theorem inner_eq_left_add_right {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (p q : EuclideanSpace ℝ (ι ⊕ κ)) :
    inner ℝ p q = inner ℝ (left p) (left q) + inner ℝ (right p) (right q) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp [left, right]

/-- The squared norm on a Euclidean orthogonal sum is the sum of the squared norms of its
two coordinate projections. -/
theorem norm_sq_eq_left_add_right {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (p : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖p‖ ^ 2 = ‖left p‖ ^ 2 + ‖right p‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_eq_left_add_right p p

/-- Projecting a left-embedded vector onto the left coordinates recovers it. -/
@[simp]
theorem left_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) :
    left (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) = z := by
  ext i
  exact EuclideanSpace.OrthogonalSum.inl_apply_inl (κ := κ) z i

/-- Projecting a left-embedded vector onto the right coordinates gives zero. -/
@[simp]
theorem right_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) :
    right (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) = 0 := by
  ext i
  exact EuclideanSpace.OrthogonalSum.inl_apply_inr (ι := ι) z i

/-- Pairing a left-embedded vector with an arbitrary direct-sum vector depends only on the
left projection. -/
theorem inner_inl_left {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) (p : EuclideanSpace ℝ (ι ⊕ κ)) :
    inner ℝ (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) p =
      inner ℝ z (left p) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp [left]

/-- The Riesz dual of a left-embedded vector is the original Riesz dual composed with the
left projection. -/
theorem toDual_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (ι ⊕ κ)))
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) =
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)) z).comp left := by
  ext p
  simp [InnerProductSpace.toDual_apply_apply, inner_inl_left]

/-- Extend a real objective to an orthogonal summand by adding half the squared norm of the
right coordinates. -/
def objective {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (f : EuclideanSpace ℝ ι → ℝ) (p : EuclideanSpace ℝ (ι ⊕ κ)) : ℝ :=
  f (left p) + ‖right p‖ ^ 2 / 2

/-- Evaluation of the objective obtained by adjoining a half squared norm on the right
orthogonal summand. -/
@[simp]
theorem objective_apply {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (f : EuclideanSpace ℝ ι → ℝ) (p : EuclideanSpace ℝ (ι ⊕ κ)) :
    objective f p = f (left p) + ‖right p‖ ^ 2 / 2 := by
  rfl

/-- The orthogonal-sum objective restricts to the original objective on the left summand. -/
@[simp]
theorem objective_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (f : EuclideanSpace ℝ ι → ℝ) (z : EuclideanSpace ℝ ι) :
    objective f (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) = f z := by
  simp [objective]

/-- A certified gradient of the left objective and the current right coordinate combine to
the gradient of the orthogonal-sum objective at an arbitrary point. -/
theorem hasGradientAt_objective {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {p : EuclideanSpace ℝ (ι ⊕ κ)} {g : EuclideanSpace ℝ ι}
    (hf : HasGradientAt f g (left p)) :
    HasGradientAt (objective (κ := κ) f)
      ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (g, right p)) p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hleft :
      HasFDerivAt (f ∘ (left (ι := ι) (κ := κ)))
        (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)) g).comp left) p :=
    hf.hasFDerivAt.comp p (left (ι := ι) (κ := κ)).hasFDerivAt
  have hright :
      HasFDerivAt (fun q : EuclideanSpace ℝ (ι ⊕ κ) => ‖right q‖ ^ 2 / 2)
        ((innerSL ℝ (right p)).comp right) p := by
    have hrightSq := ((right (ι := ι) (κ := κ)).hasFDerivAt (x := p)).norm_sq
    have hscaled := hrightSq.const_smul (2 : ℝ)⁻¹
    have hderiv :
        (2 : ℝ)⁻¹ •
            (2 • (innerSL ℝ (right (ι := ι) (κ := κ) p)).comp
              (right (ι := ι) (κ := κ))) =
          (innerSL ℝ (right (ι := ι) (κ := κ) p)).comp
            (right (ι := ι) (κ := κ)) := by
      ext x
      simp
    rw [hderiv] at hscaled
    apply hscaled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun q => by
      simp [div_eq_mul_inv, mul_comm]
  have hdual :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (ι ⊕ κ)))
          ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (g, right p)) =
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)) g).comp left +
          (innerSL ℝ (right p)).comp right := by
    ext q
    simp only [InnerProductSpace.toDual_apply_apply, add_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [inner_eq_left_add_right]
    rw [left_sumEquivProd_symm, right_sumEquivProd_symm]
  rw [hdual]
  apply (hleft.add hright).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q => by
    rfl

/-- The gradient of the orthogonal-sum objective at an arbitrary point consists of the
left gradient and the current right coordinate. -/
theorem gradient_objective {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {p : EuclideanSpace ℝ (ι ⊕ κ)} (hf : DifferentiableAt ℝ f (left p)) :
    gradient (objective (κ := κ) f) p =
      (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (gradient f (left p), right p) := by
  exact (hasGradientAt_objective (κ := κ) hf.hasGradientAt).gradient

/-- A certified gradient embeds as a certified gradient of the orthogonal-sum objective. -/
theorem hasGradientAt_objective_inl {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {z g : EuclideanSpace ℝ ι} (hf : HasGradientAt f g z) :
    HasGradientAt (objective (κ := κ) f)
      (EuclideanSpace.OrthogonalSum.inl (κ := κ) g)
      (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) := by
  rw [hasGradientAt_iff_hasFDerivAt, toDual_inl]
  have hleft :
      HasFDerivAt (f ∘ (left (ι := ι) (κ := κ)))
        (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)) g).comp
          (left (ι := ι) (κ := κ)) :
            EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] ℝ)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) := by
    have hfAtLeft :
        HasFDerivAt f ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)) g)
          (left (ι := ι) (κ := κ)
            (EuclideanSpace.OrthogonalSum.inl (κ := κ) z)) := by
      rw [left_inl]
      exact hf.hasFDerivAt
    exact hfAtLeft.comp
      (EuclideanSpace.OrthogonalSum.inl (κ := κ) z)
      (left (ι := ι) (κ := κ)).hasFDerivAt
  have hrightSq :
      HasFDerivAt (fun p : EuclideanSpace ℝ (ι ⊕ κ) =>
        ‖right (ι := ι) (κ := κ) p‖ ^ 2)
        (0 : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] ℝ)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) := by
    have hr := ((right (ι := ι) (κ := κ)).hasFDerivAt
      (x := EuclideanSpace.OrthogonalSum.inl (κ := κ) z)).norm_sq
    have hzero :
        2 • (innerSL ℝ (right (ι := ι) (κ := κ)
          (EuclideanSpace.OrthogonalSum.inl (κ := κ) z))).comp
            (right (ι := ι) (κ := κ)) = 0 := by
      simp
    rw [hzero] at hr
    exact hr
  have hright :
      HasFDerivAt (fun p : EuclideanSpace ℝ (ι ⊕ κ) =>
        ‖right (ι := ι) (κ := κ) p‖ ^ 2 / 2)
        (0 : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] ℝ)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) := by
    have hscaled := hrightSq.const_smul (2 : ℝ)⁻¹
    rw [smul_zero] at hscaled
    apply hscaled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun p => by
      simp [div_eq_mul_inv, mul_comm]
  have hadd := hleft.add hright
  rw [add_zero] at hadd
  apply hadd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun p => by
    rfl

/-- At an embedded point, the gradient of the orthogonal-sum objective is the embedded
gradient of the original objective. -/
theorem gradient_objective_inl {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {z : EuclideanSpace ℝ ι} (hf : DifferentiableAt ℝ f z) :
    gradient (objective (κ := κ) f)
        (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) =
      EuclideanSpace.OrthogonalSum.inl (κ := κ) (gradient f z) := by
  exact (hasGradientAt_objective_inl (κ := κ) hf.hasGradientAt).gradient

end EuclideanSpace.OrthogonalSum.Gradient
