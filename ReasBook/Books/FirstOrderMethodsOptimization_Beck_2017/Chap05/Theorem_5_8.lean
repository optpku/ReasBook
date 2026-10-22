/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 5.8 is `source-facing`. Domain sampling:
- mathlib owners: `DifferentiableAt`, `LipschitzOnWith`, the canonical ambient gradient `∇`,
  and `List.TFAE` for equivalence lists;
- chapter owner: Definition 5.1's `is_l_smooth_on`, specialized here to `Set.univ`;
- derived bridge: Lemma 5.7's `is_l_smooth_on_descent_lemma`, which gives clause (ii).

The primitive data are only the convex differentiable function `f` and the smoothness parameter
`L`; the quadratic upper model is derived from the owner predicate, while the lower-gradient
bound, cocoercivity inequality, and convex-combination inequality are source-facing companion
views of the same owner-level smoothness notion. The correct public shape is therefore one
`List.TFAE` theorem and not a new wrapper predicate or package. -/

section

variable [CompleteSpace E]

/-- The quadratic upper-model clause from Theorem 5.8. -/
def quadratic_upper_model (f : E → ℝ) (L : NNReal) : Prop :=
  ∀ x y : E,
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ)

/-- A quadratic upper-model hypothesis may be applied directly to a pair of points. -/
theorem quadratic_upper_model.apply {f : E → ℝ} {L : NNReal}
    (h : quadratic_upper_model f L) (x y : E) :
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) :=
  (by
    simpa [quadratic_upper_model] using h : ∀ x y : E,
      f y ≤ f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ)) x y

/-- Unfolding `quadratic_upper_model` gives exactly the displayed upper-model inequality. -/
@[simp] theorem quadratic_upper_model_iff {f : E → ℝ} {L : NNReal} :
    quadratic_upper_model f L ↔
      ∀ x y : E,
        f y ≤
          f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  simp [quadratic_upper_model]

/-- The gradient quadratic lower-bound clause from Theorem 5.8. -/
def gradient_quadratic_lower_bound (f : E → ℝ) (L : NNReal) : Prop :=
  ∀ x y : E,
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ)

/-- A gradient quadratic lower-bound hypothesis may be applied directly to a pair of points. -/
theorem gradient_quadratic_lower_bound.apply {f : E → ℝ} {L : NNReal}
    (h : gradient_quadratic_lower_bound f L) (x y : E) :
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) :=
  (by
    simpa [gradient_quadratic_lower_bound] using h : ∀ x y : E,
      f y ≥
        f x + inner ℝ (∇ f x) (y - x) +
          (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ)) x y

/-- Unfolding `gradient_quadratic_lower_bound` gives exactly the displayed lower-bound
inequality. -/
@[simp] theorem gradient_quadratic_lower_bound_iff {f : E → ℝ} {L : NNReal} :
    gradient_quadratic_lower_bound f L ↔
      ∀ x y : E,
        f y ≥
          f x + inner ℝ (∇ f x) (y - x) +
            (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) := by
  simp [gradient_quadratic_lower_bound]

/-- The gradient cocoercivity clause from Theorem 5.8. -/
def gradient_cocoercive (f : E → ℝ) (L : NNReal) : Prop :=
  ∀ x y : E,
    inner ℝ (∇ f x - ∇ f y) (x - y) ≥
      (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ)

/-- A gradient cocoercivity hypothesis may be applied directly to a pair of points. -/
theorem gradient_cocoercive.apply {f : E → ℝ} {L : NNReal}
    (h : gradient_cocoercive f L) (x y : E) :
    inner ℝ (∇ f x - ∇ f y) (x - y) ≥
      (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) :=
  (by
    simpa [gradient_cocoercive] using h : ∀ x y : E,
      inner ℝ (∇ f x - ∇ f y) (x - y) ≥
        (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ)) x y

/-- Unfolding `gradient_cocoercive` gives exactly the displayed cocoercivity inequality. -/
@[simp] theorem gradient_cocoercive_iff {f : E → ℝ} {L : NNReal} :
    gradient_cocoercive f L ↔
      ∀ x y : E,
        inner ℝ (∇ f x - ∇ f y) (x - y) ≥
          (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) := by
  simp [gradient_cocoercive]

end

/-- The convex-combination lower-bound clause from Theorem 5.8. -/
def convex_combination_quadratic_lower_bound (f : E → ℝ) (L : NNReal) : Prop :=
  ∀ x y : E, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    f (t • x + (1 - t) • y) ≥
      t * f x + (1 - t) * f y -
        ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)

/-- A convex-combination quadratic lower-bound hypothesis may be applied directly to its point,
weight, and interval-membership data. -/
theorem convex_combination_quadratic_lower_bound.apply {f : E → ℝ} {L : NNReal}
    (h : convex_combination_quadratic_lower_bound f L) (x y : E) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (t • x + (1 - t) • y) ≥
      t * f x + (1 - t) * f y -
        ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) :=
  (by
    simpa [convex_combination_quadratic_lower_bound] using h :
      ∀ x y : E, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≥
          t * f x + (1 - t) * f y -
            ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) x y t ht

/-- Unfolding `convex_combination_quadratic_lower_bound` gives exactly the displayed
convex-combination inequality. -/
@[simp] theorem convex_combination_quadratic_lower_bound_iff {f : E → ℝ} {L : NNReal} :
    convex_combination_quadratic_lower_bound f L ↔
      ∀ x y : E, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≥
          t * f x + (1 - t) * f y -
            ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) := by
  simp [convex_combination_quadratic_lower_bound]

section

variable [CompleteSpace E]

/-- Helper for Theorem 5.8: a convex differentiable function on the whole space lies above each
of its tangent planes. -/
lemma convexGradientFirstOrderLowerBound
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f) :
    ∀ x y : E, f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
  intro x y
  -- Identify the unique Euclidean subgradient at `x` with the ambient gradient `∇ f x`.
  have hsingleton :
      euclideanSubdifferentialAt f x = {∇ f x} :=
    euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
      hf_convex (hf_diff x)
  have hsub : ∇ f x ∈ euclideanSubdifferentialAt f x := by
    rw [hsingleton]
    simp
  have hsub' :
      InnerProductSpace.toDualMap ℝ E (∇ f x) ∈ subdifferentialAt f x :=
    (mem_euclideanSubdifferentialAt_iff.mp hsub)
  -- Unpack subgradient membership into the first-order support inequality.
  rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_coe_iff] at hsub'
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hsub' y

/-- Helper for Theorem 5.8: the quadratic potential `z ↦ (L / 2) * ‖z‖²` satisfies the standard
polarization identity along the chord from `x` to `y`. -/
lemma scaledNormSqLineMapIdentity {L : NNReal} (x y : E) (t : ℝ) :
    ((L : ℝ) / 2) * ‖t • x + (1 - t) • y‖ ^ (2 : ℕ) +
      ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) =
        t * (((L : ℝ) / 2) * ‖x‖ ^ (2 : ℕ)) + (1 - t) * (((L : ℝ) / 2) * ‖y‖ ^ (2 : ℕ)) := by
  -- Rewrite the convex combination as `y + t • (x - y)` so `norm_add_sq_real` applies directly.
  have hcombo : y + t • (x - y) = t • x + (1 - t) • y := by
    rw [smul_sub]
    calc
      y + (t • x - t • y) = t • x + (y - t • y) := by
        abel_nf
      _ = t • x + (1 - t) • y := by
        rw [sub_smul, one_smul]
  -- Expand both squared norms and normalize the scalar coefficients.
  rw [← hcombo, norm_add_sq_real, norm_smul, pow_two, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sub_sq_real, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_comm y x]
  ring_nf

/-- Helper for Theorem 5.8: the quadratic potential `z ↦ (L / 2) * ‖z‖²` has gradient
`z ↦ L • z`. -/
lemma quadraticPotentialHasGradientAt {L : NNReal} (x : E) :
    HasGradientAt (fun z : E ↦ ((L : ℝ) / 2) * ‖z‖ ^ (2 : ℕ)) ((L : ℝ) • x) x := by
  -- Differentiate `‖z‖²` and absorb the factor `L / 2`.
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul ((L : ℝ) / 2) using 1
  ext z
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, InnerProductSpace.toDual_apply_apply]

/-- Helper for Theorem 5.8: the quadratic upper model implies the gradient quadratic lower bound
for a convex differentiable function. -/
lemma gradientQuadraticLowerBound_of_quadraticUpperModel
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    {L : NNReal} (hL : 0 < L) :
    quadratic_upper_model f L → gradient_quadratic_lower_bound f L := by
  intro hupper x y
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL
  have hLinv_nonneg : 0 ≤ 1 / (L : ℝ) := by
    positivity
  let Δ := ∇ f x - ∇ f y
  let z := y + (1 / (L : ℝ)) • Δ
  -- Compare the support inequality at `x` with the upper model at the gradient step from `y`.
  have hsupport := convexGradientFirstOrderLowerBound hf_convex hf_diff x z
  have hupper' := quadratic_upper_model.apply hupper y z
  have hmain :
      f x + inner ℝ (∇ f x) (z - x) ≤
        f y + inner ℝ (∇ f y) (z - y) + ((L : ℝ) / 2) * ‖y - z‖ ^ (2 : ℕ) := by
    linarith
  have hz : z - y = (1 / (L : ℝ)) • Δ := by
    simp [z, Δ]
  have hyz : y - z = -((1 / (L : ℝ)) • Δ) := by
    simp [z, Δ, sub_eq_add_neg]
  have hxz : z - x = y - x + (1 / (L : ℝ)) • Δ := by
    simp [z, Δ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hxz, hz, hyz, inner_add_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_of_nonneg hLinv_nonneg, pow_two] at hmain
  -- The explicit step size turns the inner-product difference into `‖Δ‖²`.
  have hgy : inner ℝ (∇ f y) ((1 / (L : ℝ)) • Δ) = (1 / (L : ℝ)) * inner ℝ (∇ f y) Δ := by
    rw [inner_smul_right]
  rw [hgy] at hmain
  have hinnerΔ : inner ℝ (∇ f x) Δ - inner ℝ (∇ f y) Δ = ‖Δ‖ ^ (2 : ℕ) := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hstep :
      (1 / (L : ℝ)) * inner ℝ (∇ f x) Δ =
        (1 / (L : ℝ)) * inner ℝ (∇ f y) Δ + (1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ) := by
    nlinarith [hinnerΔ]
  have hquad :
      ((L : ℝ) / 2) * ((1 / (L : ℝ)) * ‖Δ‖ * ((1 / (L : ℝ)) * ‖Δ‖)) =
        (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) := by
    field_simp [hLreal.ne']
  rw [hstep, hquad] at hmain
  ring_nf at hmain
  -- Cancel the common linear term and split `1 / L` as two copies of `1 / (2L)`.
  have hcancel :
      f x + inner ℝ (∇ f x) (y - x) + (1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ) ≤
        (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) + f y := by
    have hmain' :
        (f x + inner ℝ (∇ f x) (y - x) + (1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ)) +
            ((L : ℝ)⁻¹ * inner ℝ (∇ f y) Δ) ≤
          ((1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) + f y) +
            ((L : ℝ)⁻¹ * inner ℝ (∇ f y) Δ) := by
      simpa [add_assoc, add_left_comm, add_comm, one_div, mul_assoc, mul_left_comm, mul_comm]
        using hmain
    exact (add_le_add_iff_right ((L : ℝ)⁻¹ * inner ℝ (∇ f y) Δ)).mp hmain'
  have hdouble :
      (1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ) =
        (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) := by
    field_simp [hLreal.ne']
    ring
  rw [hdouble] at hcancel
  have hdesired' :
      (f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ)) +
          (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) ≤
        f y + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using hcancel
  have hdesired :
      f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ) ≤ f y := by
    exact (add_le_add_iff_right ((1 / (2 * (L : ℝ))) * ‖Δ‖ ^ (2 : ℕ))).mp hdesired'
  simpa [Δ] using hdesired

/-- Helper for Theorem 5.8: the quadratic lower bound on `f` implies the gradient cocoercivity
clause by adding the two directional inequalities. -/
lemma gradientCocoercive_of_gradientQuadraticLowerBound
    {f : E → ℝ} {L : NNReal} :
    gradient_quadratic_lower_bound f L → gradient_cocoercive f L := by
  intro hquad x y
  -- Add the lower bounds at `(x, y)` and `(y, x)` after normalizing the symmetric terms.
  have hxy := gradient_quadratic_lower_bound.apply hquad x y
  have hyx :
      f x ≥
        f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) := by
    simpa [norm_sub_rev] using gradient_quadratic_lower_bound.apply hquad y x
  have hlinear :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) =
        -inner ℝ (∇ f x - ∇ f y) (x - y) := by
    calc
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)
          = -inner ℝ (∇ f x) (x - y) + inner ℝ (∇ f y) (x - y) := by
              rw [show y - x = -(x - y) by abel_nf, inner_neg_right]
      _ = -(inner ℝ (∇ f x) (x - y) - inner ℝ (∇ f y) (x - y)) := by
            ring
      _ = -inner ℝ (∇ f x - ∇ f y) (x - y) := by
            rw [← inner_sub_left]
  let a : ℝ := (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ)
  have hxy' : 0 ≤ f y - f x - inner ℝ (∇ f x) (y - x) - a := by
    dsimp [a]
    linarith
  have hyx' : 0 ≤ f x - f y - inner ℝ (∇ f y) (x - y) - a := by
    dsimp [a]
    linarith
  have hsum :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) +
        (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤ 0 := by
    have hsum0 := add_nonneg hxy' hyx'
    dsimp [a] at hsum0
    ring_nf at hsum0
    have hsum' :
        inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) +
          ((L : ℝ)⁻¹) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤ 0 := by
      linarith
    simpa [one_div] using hsum'
  rw [hlinear] at hsum
  nlinarith

/-- Helper for Theorem 5.8: gradient cocoercivity upgrades to global `L`-smoothness by combining
it with Cauchy-Schwarz to recover the gradient Lipschitz estimate from Definition 5.1. -/
lemma lSmooth_of_gradientCocoercive
    {f : E → ℝ} (hf_diff : Differentiable ℝ f)
    {L : NNReal} (hL : 0 < L) :
    gradient_cocoercive f L → is_l_smooth_on f Set.univ L := by
  intro hcoco
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨fun x _ ↦ hf_diff x, ?_⟩
  intro x _ y _
  let Δ := ∇ f x - ∇ f y
  have hcoco' := gradient_cocoercive.apply hcoco x y
  have hcs : inner ℝ Δ (x - y) ≤ ‖Δ‖ * ‖x - y‖ := by
    simpa [Δ] using real_inner_le_norm Δ (x - y)
  by_cases hΔ : ‖Δ‖ = 0
  · -- When the gradient difference vanishes, the Lipschitz bound is immediate.
    have hnonneg : 0 ≤ (L : ℝ) * ‖x - y‖ := by
      positivity
    simpa [Δ, hΔ] using hnonneg
  · have hΔpos : 0 < ‖Δ‖ := by
      exact lt_of_le_of_ne (norm_nonneg Δ) (by simpa [eq_comm] using hΔ)
    have hbound :
        (1 / (L : ℝ)) * ‖Δ‖ ^ (2 : ℕ) ≤ ‖Δ‖ * ‖x - y‖ := by
      exact le_trans hcoco' hcs
    have hbound' : ((1 / (L : ℝ)) * ‖Δ‖) * ‖Δ‖ ≤ ‖x - y‖ * ‖Δ‖ := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hbound
    have hcancel : (1 / (L : ℝ)) * ‖Δ‖ ≤ ‖x - y‖ := by
      exact le_of_mul_le_mul_right hbound' hΔpos
    have hfinal : ‖Δ‖ ≤ (L : ℝ) * ‖x - y‖ := by
      have hdiv : ‖Δ‖ / (L : ℝ) ≤ ‖x - y‖ := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcancel
      have hfinal' := (div_le_iff₀ hLreal).mp hdiv
      simpa [mul_comm] using hfinal'
    simpa [Δ] using hfinal

/-- Helper for Theorem 5.8: the quadratic upper model implies the convex-combination lower bound
by applying the model at the chord point and averaging the two endpoint inequalities. -/
lemma convexCombinationLowerBound_of_quadraticUpperModel
    {f : E → ℝ} {L : NNReal} :
    quadratic_upper_model f L → convex_combination_quadratic_lower_bound f L := by
  intro hupper x y t ht
  rcases ht with ⟨ht0, ht1⟩
  let xt : E := t • x + (1 - t) • y
  have hxt : xt = t • x + (1 - t) • y := rfl
  -- Apply the upper model at the chord point against both endpoints.
  have hx := quadratic_upper_model.apply hupper xt x
  have hy := quadratic_upper_model.apply hupper xt y
  have hx' := mul_le_mul_of_nonneg_left hx ht0
  have hy' := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr ht1)
  have hsum := add_le_add hx' hy'
  have hxdecomp : x = t • x + (1 - t) • x := by
    calc
      x = (1 : ℝ) • x := by rw [one_smul]
      _ = (t + (1 - t)) • x := by congr 1; ring
      _ = t • x + (1 - t) • x := by rw [add_smul]
  have hydecomp : y = t • y + (1 - t) • y := by
    calc
      y = (1 : ℝ) • y := by rw [one_smul]
      _ = (t + (1 - t)) • y := by congr 1; ring
      _ = t • y + (1 - t) • y := by rw [add_smul]
  have hxsub : x - xt = (1 - t) • (x - y) := by
    rw [hxt]
    calc
      x - (t • x + (1 - t) • y) = (x - t • x) - (1 - t) • y := by
        abel_nf
      _ = (1 - t) • x - (1 - t) • y := by
        have hxminus : x - t • x = (1 - t) • x := by
          have hxminus' : x - t • x = (t • x + (1 - t) • x) - t • x := by
            exact congrArg (fun z : E => z - t • x) hxdecomp
          rw [hxminus']
          abel_nf
        rw [hxminus]
      _ = (1 - t) • (x - y) := by rw [← smul_sub]
  have hysub : y - xt = (-t) • (x - y) := by
    rw [hxt]
    calc
      y - (t • x + (1 - t) • y) = (y - (1 - t) • y) - t • x := by
        abel_nf
      _ = t • y - t • x := by
        have hycancel : y - (1 - t) • y = t • y := by
          have hycancel' : y - (1 - t) • y = (t • y + (1 - t) • y) - (1 - t) • y := by
            exact congrArg (fun z : E => z - (1 - t) • y) hydecomp
          rw [hycancel']
          abel_nf
        rw [hycancel]
      _ = -(t • x - t • y) := by
        simpa [sub_eq_add_neg] using (neg_sub (t • x) (t • y)).symm
      _ = -(t • (x - y)) := by rw [smul_sub]
      _ = (-t) • (x - y) := by
        simpa using (neg_smul t (x - y)).symm
  have hxtx : xt - x = -((1 - t) • (x - y)) := by
    calc
      xt - x = -(x - xt) := by abel_nf
      _ = -((1 - t) • (x - y)) := by rw [hxsub]
  have hxty : xt - y = t • (x - y) := by
    calc
      xt - y = -(y - xt) := by abel_nf
      _ = -((-t) • (x - y)) := by rw [hysub]
      _ = t • (x - y) := by simp
  have hlin :
      t * inner ℝ (∇ f xt) (x - xt) + (1 - t) * inner ℝ (∇ f xt) (y - xt) = 0 := by
    -- The weighted linear corrections cancel because the chord point is `t x + (1 - t) y`.
    rw [hxsub, hysub, inner_smul_right, inner_smul_right]
    ring
  have hquad :
      t * (((L : ℝ) / 2) * ‖xt - x‖ ^ (2 : ℕ)) +
        (1 - t) * (((L : ℝ) / 2) * ‖xt - y‖ ^ (2 : ℕ)) =
          ((L : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) := by
    -- Both quadratic remainders reduce to the same `‖x - y‖²` term with complementary weights.
    rw [hxtx, hxty, norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1),
      Real.norm_of_nonneg ht0]
    ring_nf
  -- Normalize the weighted sum into the displayed convex-combination inequality.
  ring_nf at hsum
  ring_nf
  linarith [hsum, hlin, hquad]

/-- Helper for Theorem 5.8: the convex-combination clause is exactly Jensen convexity for the
quadratic potential `z ↦ ((L : ℝ) / 2) * ‖z‖² - f z`. -/
lemma quadraticPotentialSub_convexOn_of_convexCombinationLowerBound
    {f : E → ℝ} {L : NNReal} :
    convex_combination_quadratic_lower_bound f L →
      ConvexOn ℝ Set.univ (fun z : E ↦ ((L : ℝ) / 2) * ‖z‖ ^ (2 : ℕ) - f z) := by
  intro hcombo
  refine ⟨by simpa using (convex_univ : Convex ℝ (Set.univ : Set E)), ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by
    linarith
  rw [hb_eq]
  have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ha
    · linarith
  have hcombo' := convex_combination_quadratic_lower_bound.apply hcombo x y ha_mem
  have hquad := scaledNormSqLineMapIdentity (L := L) x y a
  -- Route correction: rewrite clause (v) as Jensen convexity for the quadratic potential minus `f`.
  have hfinal :
      ((L : ℝ) / 2) * ‖a • x + (1 - a) • y‖ ^ (2 : ℕ) -
          f (a • x + (1 - a) • y) ≤
        a * ((((L : ℝ) / 2) * ‖x‖ ^ (2 : ℕ)) - f x) +
          (1 - a) * ((((L : ℝ) / 2) * ‖y‖ ^ (2 : ℕ)) - f y) := by
    linarith
  simpa [sub_eq_add_neg, smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    using hfinal

/-- Helper for Theorem 5.8: once the quadratic potential minus `f` is convex, its first-order
support inequality rearranges back to the quadratic upper model for `f`. -/
lemma quadraticUpperModel_of_convexCombinationLowerBound
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_diff : Differentiable ℝ f)
    {L : NNReal} :
    convex_combination_quadratic_lower_bound f L → quadratic_upper_model f L := by
  intro hcombo
  let g : E → ℝ := fun z ↦ ((L : ℝ) / 2) * ‖z‖ ^ (2 : ℕ) - f z
  have hg_convex :
      ConvexOn ℝ Set.univ g :=
    quadraticPotentialSub_convexOn_of_convexCombinationLowerBound hcombo
  have hg_gradAt :
      ∀ z : E, HasGradientAt g (((L : ℝ) • z) - ∇ f z) z := by
    intro z
    -- Differentiate the quadratic potential and subtract the gradient of `f`.
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [g, sub_eq_add_neg] using
      (quadraticPotentialHasGradientAt (L := L) z).hasFDerivAt.sub
        ((hf_diff z).hasGradientAt.hasFDerivAt)
  have hg_diff : Differentiable ℝ g := by
    intro z
    exact (hg_gradAt z).differentiableAt
  intro x y
  have hsupport := convexGradientFirstOrderLowerBound hg_convex hg_diff x y
  have hgx : ∇ g x = ((L : ℝ) • x) - ∇ f x := by
    exact (hg_gradAt x).gradient
  have hinner :
      inner ℝ (((L : ℝ) • x) - ∇ f x) (y - x) =
        inner ℝ ((L : ℝ) • x) (y - x) - inner ℝ (∇ f x) (y - x) := by
    rw [inner_sub_left]
  have hquadratic :
      ((L : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) =
        ((L : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) +
          inner ℝ ((L : ℝ) • x) (y - x) +
          ((L : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    -- This is the exact quadratic Taylor expansion of `z ↦ (L / 2) * ‖z‖²`.
    rw [norm_sub_sq_real, inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
    simp
    ring
  have hsupport' :
      ((L : ℝ) / 2) * ‖y‖ ^ (2 : ℕ) - f y ≥
        ((L : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) - f x +
          inner ℝ (((L : ℝ) • x) - ∇ f x) (y - x) := by
    simpa [g, hgx] using hsupport
  linarith

-- Proof sketch: use Definition 5.1 to identify clause (i) with global Lipschitz control of the
-- derivative/gradient. Then combine the descent lemma with the standard Baillon-Haddad style
-- implications for convex differentiable functions to prove
-- `(i) → (ii) → (iii) → (iv) → (i)`,
-- and show `(ii) ↔ (v)` by applying the upper quadratic model at the convex combination point and
-- passing to the endpoint limit in the reverse direction.
/-- Theorem 5.8: for a convex differentiable real-valued function and a positive smoothness
parameter `L`, the following are equivalent: (i) `f` is globally `L`-smooth, (ii) `f` satisfies
the quadratic upper model, (iii) `f` satisfies the quadratic lower bound in terms of gradient
differences, (iv) the gradient is `1 / L`-cocoercive, and (v) the convex-combination inequality is
relaxed by the quadratic error term `L / 2 * λ * (1 - λ) * ‖x - y‖²`. The ambient
differentiability hypothesis ensures that `∇ f` agrees everywhere with the actual derivative,
rather than with mathlib's default zero value at nondifferentiable points. -/
theorem convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    (L : NNReal) (hL : 0 < L) :
    List.TFAE
      [is_l_smooth_on f Set.univ L,
        quadratic_upper_model f L,
        gradient_quadratic_lower_bound f L,
        gradient_cocoercive f L,
        convex_combination_quadratic_lower_bound f L] := by
  -- Route correction: assemble the theorem from clause-surface implications, so the main proof is
  -- only TFAE bookkeeping and all algebra stays in the dedicated helpers above.
  tfae_have 1 → 2 := by
    intro hsmooth
    -- Clause (i) implies the descent-style quadratic upper model via Lemma 5.7.
    exact is_l_smooth_on_univ_descent_lemma hsmooth
  tfae_have 2 → 3 := by
    intro hupper
    -- The existing quadratic upper-model helper yields the gradient lower bound.
    exact gradientQuadraticLowerBound_of_quadraticUpperModel hf_convex hf_diff hL hupper
  tfae_have 3 → 4 := by
    intro hquad
    -- Add the two directional lower bounds to obtain gradient cocoercivity.
    exact gradientCocoercive_of_gradientQuadraticLowerBound hquad
  tfae_have 4 → 1 := by
    intro hcoco
    -- Recover Definition 5.1 through the gradient Lipschitz estimate.
    exact lSmooth_of_gradientCocoercive hf_diff hL hcoco
  tfae_have 2 → 5 := by
    intro hupper
    -- Average the endpoint upper models at the chord point.
    exact convexCombinationLowerBound_of_quadraticUpperModel hupper
  tfae_have 5 → 2 := by
    intro hcombo
    -- Apply the support inequality to the convex quadratic potential minus `f`.
    exact quadraticUpperModel_of_convexCombinationLowerBound hf_diff hcombo
  tfae_finish

/-- Theorem 5.8 companion: for a convex differentiable function, global `L`-smoothness is
equivalent to the quadratic upper model. -/
theorem convex_l_smooth_iff_quadratic_upper_model
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    {L : NNReal} :
    is_l_smooth_on f Set.univ L ↔ quadratic_upper_model f L := by
  by_cases hL : 0 < L
  · exact
      List.TFAE.out
        (convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
          f hf_convex hf_diff L hL)
        0 1
        (by rfl)
        (by rfl)
  · have hL0 : L = 0 := le_antisymm (not_lt.mp hL) (by positivity)
    subst hL0
    constructor
    · intro hf_smooth x y
      simpa using is_l_smooth_on_univ_descent_lemma hf_smooth x y
    · intro hupper
      have hsupport : ∀ x y : E, f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
        intro x y
        have hsingleton :
            euclideanSubdifferentialAt f x = {∇ f x} :=
          euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
            hf_convex (hf_diff x)
        have hsub :
            ∇ f x ∈ euclideanSubdifferentialAt f x := by
          rw [hsingleton]
          simp
        have hsub' :
            InnerProductSpace.toDualMap ℝ E (∇ f x) ∈ subdifferentialAt f x :=
          (mem_euclideanSubdifferentialAt_iff.mp hsub)
        rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
          is_subgradient_at_coe_iff] at hsub'
        simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hsub' y
      have haffine : ∀ x y : E, f y = f x + inner ℝ (∇ f x) (y - x) := by
        intro x y
        refine le_antisymm ?_ (hsupport x y)
        simpa using quadratic_upper_model.apply hupper x y
      have hgrad_eq : ∀ x y : E, ∇ f x = ∇ f y := by
        intro x y
        apply (InnerProductSpace.toDualMap ℝ E).injective
        ext v
        have hxv : f (x + v) = f x + inner ℝ (∇ f x) v := by
          simpa using haffine x (x + v)
        have hyx : f x = f y + inner ℝ (∇ f y) (x - y) := haffine y x
        have hyv :
            f (x + v) = f y + inner ℝ (∇ f y) (x - y) + inner ℝ (∇ f y) v := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_add_right] using
            haffine y (x + v)
        have hinner : inner ℝ (∇ f x) v = inner ℝ (∇ f y) v := by
          linarith
        simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hinner
      rw [is_l_smooth_on_iff]
      refine ⟨fun x _ ↦ hf_diff x, ?_⟩
      intro x _ y _
      have hderiv_eq : fderiv ℝ f x = fderiv ℝ f y := by
        rw [(hf_diff x).hasGradientAt.hasFDerivAt.fderiv,
          (hf_diff y).hasGradientAt.hasFDerivAt.fderiv, hgrad_eq x y]
      simp [hderiv_eq]

/-- Theorem 5.8 companion: for a convex differentiable function, global `L`-smoothness is
equivalent to the gradient quadratic lower bound. -/
theorem convex_l_smooth_iff_gradient_quadratic_lower_bound
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    {L : NNReal} (hL : 0 < L) :
    is_l_smooth_on f Set.univ L ↔ gradient_quadratic_lower_bound f L := by
  exact
    List.TFAE.out
      (convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
        f hf_convex hf_diff L hL)
      0 2
      (by rfl)
      (by rfl)

/-- Theorem 5.8 companion: for a convex differentiable function, global `L`-smoothness is
equivalent to gradient cocoercivity with constant `1 / L`. -/
theorem convex_l_smooth_iff_gradient_cocoercive
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    {L : NNReal} (hL : 0 < L) :
    is_l_smooth_on f Set.univ L ↔ gradient_cocoercive f L := by
  exact
    List.TFAE.out
      (convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
        f hf_convex hf_diff L hL)
      0 3
      (by rfl)
      (by rfl)

/-- Theorem 5.8 companion: for a convex differentiable function, global `L`-smoothness is
equivalent to the convex-combination quadratic lower bound. -/
theorem convex_l_smooth_iff_convex_combination_quadratic_lower_bound
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f)
    {L : NNReal} (hL : 0 < L) :
    is_l_smooth_on f Set.univ L ↔ convex_combination_quadratic_lower_bound f L := by
  exact
    List.TFAE.out
      (convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
        f hf_convex hf_diff L hL)
      0 4
      (by rfl)
      (by rfl)

/-- Convex global `L`-smoothness implies the gradient cocoercivity clause from Theorem 5.8. The
differentiability hypothesis is derived from `is_l_smooth_on`, so callers only supply convexity,
smoothness, and positivity of `L`. -/
theorem gradient_cocoercive_of_convex_l_smooth
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) {L : NNReal}
    (hf_smooth : is_l_smooth_on f Set.univ L) (hL : 0 < L) :
    gradient_cocoercive f L := by
  have hf_diff : Differentiable ℝ f := by
    intro x
    exact hf_smooth.1 x (by simp)
  exact (convex_l_smooth_iff_gradient_cocoercive hf_convex hf_diff hL).mp hf_smooth

end
