/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

attribute [local instance] Classical.propDecidable

section

/-- Helper for Example 6.21: the scalar penalty `nonnegative_linear_penalty μ` is lower
semicontinuous. -/
private theorem lowerSemicontinuousNonnegativeLinearPenalty (mu : ℝ) :
    LowerSemicontinuous (nonnegative_linear_penalty mu) := by
  -- Rewrite the epigraph into an explicit closed half-space intersection.
  rw [lowerSemicontinuous_iff_isClosed_real_epigraph]
  have hepigraph :
      realEpigraph (nonnegative_linear_penalty mu) =
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ mu * p.1 ≤ p.2} := by
    ext p
    change nonnegative_linear_penalty mu p.1 ≤ (p.2 : EReal) ↔ 0 ≤ p.1 ∧ mu * p.1 ≤ p.2
    by_cases hp : 0 ≤ p.1
    · rw [nonnegative_linear_penalty_apply, if_pos hp]
      rw [EReal.coe_mul]
      constructor
      · intro h
        exact ⟨hp, EReal.coe_le_coe_iff.mp h⟩
      · intro h
        exact EReal.coe_le_coe_iff.mpr h.2
    · simp [nonnegative_linear_penalty_apply, hp]
  rw [hepigraph]
  -- Each constraint set is closed, so their intersection is closed.
  have hnonneg : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hlinear : IsClosed {p : ℝ × ℝ | mu * p.1 ≤ p.2} :=
    isClosed_le (continuous_const.mul continuous_fst) continuous_snd
  simpa [Set.setOf_and] using hnonneg.inter hlinear

/-- Helper for Example 6.21: the scalar penalty `nonnegative_linear_penalty μ` is convex. -/
private theorem isConvexNonnegativeLinearPenalty (mu : ℝ) :
    is_convex_function (nonnegative_linear_penalty mu) := by
  -- Decompose the penalty into the indicator of `[0, ∞)` plus a linear function.
  have hind : is_convex_function (extendedIndicator (Set.Ici (0 : ℝ))) := by
    have hconv : Convex ℝ (realEpigraph (δ_ (Set.Ici (0 : ℝ)))) := by
      rw [extendedIndicator_real_epigraph_eq]
      simpa using (convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ))
    simpa [is_convex_function, realEpigraph] using hconv
  have hlin : is_convex_function ((fun t : ℝ ↦ mu * t).toEReal) := by
    exact Function.toEReal_isConvexFunction <| by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      change mu * (a * x + b * y) ≤ a * (mu * x) + b * (mu * y)
      nlinarith [hab]
  -- The pointwise sum matches `nonnegative_linear_penalty`.
  simpa [nonnegative_linear_penalty, Function.toEReal, Pi.add_apply] using
    is_convex_function_pointwise_add hind hlin
      (by
        intro t
        by_cases ht : 0 ≤ t
        · simp [extendedIndicator, ht]
        · have ht' : t ∈ Set.Iio (0 : ℝ) := by
            simpa using ht
          simp [extendedIndicator, ht'])
      (by
        intro t
        exact EReal.coe_ne_bot _)

/-- Helper for Example 6.21: on the nonnegative ray, the scalar proximal mapping for
`nonnegative_linear_penalty (-lam)` is the singleton `{t + lam}`. -/
private theorem proxNonnegativeLinearPenaltyNegEqSingletonAddOfNonneg
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t) :
    prox[nonnegative_linear_penalty (-lam)] t = {t + lam} := by
  -- Start from the scalar Chapter 6 proximal formula and simplify the positive part.
  calc
    prox[nonnegative_linear_penalty (-lam)] t = {(t - (-lam))⁺} := by
      simpa using prox_nonnegative_linear_penalty_eq_singleton_posPart_sub (-lam) t
    _ = {t + lam} := by
      rw [Set.singleton_eq_singleton_iff]
      rw [sub_eq_add_neg]
      simp [posPart_eq_self.2 (add_nonneg ht (le_of_lt hlam))]

/- Example 6.21 is `source-facing` in the Chapter 6 proximal-operator domain. Domain sampling
against the chapter owner `prox[...]` from Definition 6.1, the source-facing penalty owner
`norm_penalty` from Example 6.19, the radial owner theorem
`prox_norm_composition_eq_piecewise` from Theorem 6.18, and the scalar proximal formula
`prox_nonnegative_linear_penalty_eq_singleton_posPart_sub` from Lemma 6.5 shows that the
primitive data here is already fixed upstream: the penalty is exactly `norm_penalty (-lam)`.
The sphere/singleton description is derived API for that owner. Its singleton branch is Euclidean,
so the statement belongs in the inner-product owner layer rather than in an arbitrary real normed
space. -/
-- Semantic recall: `lean_leansearch` produced no direct useful hit for this proximal formula, so
-- the owner/API choice is verified from the local Chapter 6 precedent above.

-- Proof sketch: in a real inner product space, minimize
-- `u ↦ -λ ‖u‖ + (1 / 2) ‖u - x‖^2` by reducing to the radial variable `r = ‖u‖`. For `x ≠ 0`,
-- equality in the triangle inequality forces any minimizer to lie on the ray through `x`, where
-- the scalar problem becomes the proximal problem for `t ↦ -λ t` on `[0, ∞)`, giving the radius
-- `‖x‖ + λ` and hence the unique point `(1 + λ / ‖x‖) • x`. For `x = 0`, the objective depends
-- only on `‖u‖`, so every point with norm `λ` is a minimizer.
/-- Example 6.21 (prox of negative Euclidean norm): let `f : E → ℝ` be given by
`f x = -lam * ‖x‖`, where `0 < lam`. Then the proximal mapping `prox[f] x` is
`Metric.sphere 0 lam` at the origin and the singleton `{(1 + lam / ‖x‖) • x}` away from the
origin. -/
theorem prox_norm_penalty_neg_eq_piecewise (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[norm_penalty (-lam)] x =
      if x = 0 then Metric.sphere 0 lam else {(1 + lam / ‖x‖) • x} := by
  -- Route correction: specialize the radial composition theorem to
  -- `g = nonnegative_linear_penalty (-lam)` and simplify the scalar proximal sets.
  have hpiece :=
    prox_norm_composition_eq_piecewise
      (nonnegative_linear_penalty (-lam))
      (isProper_nonnegative_linear_penalty (-lam))
      (lowerSemicontinuousNonnegativeLinearPenalty (-lam))
      (isConvexNonnegativeLinearPenalty (-lam))
      (fun t ht ↦ by simp [nonnegative_linear_penalty_apply, not_le_of_gt ht])
      x
  have hprox :
      prox[norm_penalty (-lam)] x =
        if x = 0 then
          {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty (-lam)] 0}
        else
          (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty (-lam)] ‖x‖ := by
    -- Replace the vector penalty by its scalar radial profile.
    calc
      prox[norm_penalty (-lam)] x =
          prox[nonnegative_linear_penalty (-lam) ∘ (norm : E → ℝ)] x := by
        exact congrArg (fun f : E → EReal ↦ prox[f] x)
          (norm_penalty_eq_nonnegative_linear_penalty_comp_norm (-lam))
      _ = if x = 0 then
            {u : E | ‖u‖ ∈ prox[nonnegative_linear_penalty (-lam)] 0}
          else
            (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty (-lam)] ‖x‖ := hpiece
  rw [hprox]
  by_cases hx : x = 0
  · rw [if_pos hx]
    subst x
    -- At the origin, the scalar proximal radius is `lam`, so the proximal set is the sphere.
    have hscalar0 :
        prox[nonnegative_linear_penalty (-lam)] 0 = {lam} := by
      simpa using proxNonnegativeLinearPenaltyNegEqSingletonAddOfNonneg lam 0 hlam le_rfl
    ext u
    rw [hscalar0]
    simp
  · suffices hbranch :
        (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty (-lam)] ‖x‖ =
          {(1 + lam / ‖x‖) • x} by
      simpa [hx] using hbranch
    -- Away from the origin, the scalar prox radius is `‖x‖ + lam` and lifts along the ray of `x`.
    have hscalar :
        prox[nonnegative_linear_penalty (-lam)] ‖x‖ = {‖x‖ + lam} := by
      exact proxNonnegativeLinearPenaltyNegEqSingletonAddOfNonneg lam ‖x‖ hlam (norm_nonneg x)
    have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcoeff : ((‖x‖ + lam) / ‖x‖ : ℝ) = 1 + lam / ‖x‖ := by
      field_simp [hnorm_pos.ne']
    calc
      (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[nonnegative_linear_penalty (-lam)] ‖x‖
          = {(((‖x‖ + lam) / ‖x‖) • x)} := by
              rw [hscalar]
              simp
      _ = {(1 + lam / ‖x‖) • x} := by
            rw [Set.singleton_eq_singleton_iff]
            simp [hcoeff]

-- Proof sketch: specialize the source-facing piecewise formula to `x = 0`, where the `if`
-- reduces to the sphere branch.
/-- At the origin, the proximal mapping of `x ↦ -lam ‖x‖` is exactly the sphere of radius `lam`. -/
@[simp] theorem prox_norm_penalty_neg_at_zero (lam : ℝ) (hlam : 0 < lam) :
    prox[norm_penalty (-lam)] (0 : E) = Metric.sphere 0 lam := by
  simpa using prox_norm_penalty_neg_eq_piecewise lam hlam (0 : E)

-- Proof sketch: rewrite by `prox_norm_penalty_neg_at_zero`; membership in the sphere centered at
-- `0` is exactly the norm constraint `‖u‖ = lam`.
/-- A vector belongs to `prox[norm_penalty (-lam)] 0` exactly when it has norm `lam`. -/
@[simp] theorem mem_prox_norm_penalty_neg_at_zero_iff
    (lam : ℝ) (hlam : 0 < lam) {u : E} :
    u ∈ prox[norm_penalty (-lam)] (0 : E) ↔ ‖u‖ = lam := by
  rw [prox_norm_penalty_neg_at_zero lam hlam]
  simp

-- Proof sketch: specialize the source-facing piecewise formula away from the origin, where the
-- `if` reduces to the singleton branch.
/-- Away from the origin, the proximal mapping of `x ↦ -lam ‖x‖` is the singleton
`{(1 + lam / ‖x‖) • x}`. -/
theorem prox_norm_penalty_neg_of_ne_zero
    (lam : ℝ) (hlam : 0 < lam) {x : E} (hx : x ≠ 0) :
    prox[norm_penalty (-lam)] x = {(1 + lam / ‖x‖) • x} := by
  simpa [hx] using prox_norm_penalty_neg_eq_piecewise lam hlam x

-- Proof sketch: rewrite by `prox_norm_penalty_neg_of_ne_zero`; membership in a singleton is
-- equality with its center.
/-- Away from the origin, a vector belongs to `prox[norm_penalty (-lam)] x` exactly when it equals
the unique proximal point `(1 + lam / ‖x‖) • x`. -/
@[simp] theorem mem_prox_norm_penalty_neg_of_ne_zero_iff
    (lam : ℝ) (hlam : 0 < lam) {x u : E} (hx : x ≠ 0) :
    u ∈ prox[norm_penalty (-lam)] x ↔ u = (1 + lam / ‖x‖) • x := by
  rw [prox_norm_penalty_neg_of_ne_zero lam hlam hx]
  simp

end

end
