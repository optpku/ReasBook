/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: smooth strongly convex objectives on real Hilbert spaces.

Relevant owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.gradient_strong_mono` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.lower_tangent_quadratic` in `Definition_2_17`
* `IsStrongConvexSmoothObjective.upper_tangent_quadratic` in `Definition_2_17`

Owner-layer triage:
* source-facing: Theorem 2.13 on `ℝⁿ`
* core/canonical: `IsStrongConvexSmoothObjective μ L f`
* bridge/view: the Euclidean specialization used later in Chapter 2

Primitive data in the owner abstraction:
* positivity of `μ`
* global `C¹` regularity
* `μ`-strong convexity on the whole space
* the `L`-gradient-Lipschitz bound

Derived API:
* strong gradient monotonicity
* the secant inequality below

The strengthened secant inequality is therefore kept as owner-derived API in the namespace
`IsStrongConvexSmoothObjective`, rather than through a second Euclidean wrapper. -/

namespace IsStrongConvexSmoothObjective

variable {μ L : ℝ} {f : E → ℝ}

/-- Helper for Theorem 2.13: the shifted objective `z ↦ f z - (μ / 2) * ‖z‖²`. -/
private abbrev shiftedObjective (μ : ℝ) (f : E → ℝ) : E → ℝ :=
  fun z ↦ f z - (μ / 2) * ‖z‖ ^ (2 : ℕ)

/-- Helper for Theorem 2.13: the explicit gradient field of the shifted objective. -/
private abbrev shiftedGradient (μ : ℝ) (f : E → ℝ) : E → E :=
  fun z ↦ ∇ f z - μ • z

/-- Helper for Theorem 2.13: the quadratic shift `z ↦ (μ / 2) * ‖z‖²` has gradient `μ • z`. -/
private theorem shiftedQuadratic_hasFDerivAt
    (μ : ℝ) (x : E) :
    HasFDerivAt (fun u : E ↦ (μ / 2) * ‖u‖ ^ (2 : ℕ))
      (InnerProductSpace.toDual ℝ E (μ • x)) x := by
  -- Compute the Fréchet derivative of `‖·‖²` and scale it by `μ / 2`.
  have hsmul :
      HasFDerivAt (fun u : E ↦ (μ / 2) * ‖u‖ ^ (2 : ℕ))
        (((μ / 2) • (2 • innerSL ℝ x)) : E →L[ℝ] ℝ) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (μ / 2)
  have hlin :
      (((μ / 2) • (2 • innerSL ℝ x)) : E →L[ℝ] ℝ) =
        InnerProductSpace.toDual ℝ E (μ • x) := by
    ext u
    simp [InnerProductSpace.toDual_apply_apply, two_smul]
    ring
  exact hlin ▸ hsmul

/-- Helper for Theorem 2.13: the shifted objective has explicit gradient
`z ↦ ∇ f z - μ • z`. -/
private theorem shiftedObjective_hasGradientAt
    (hf : IsStrongConvexSmoothObjective μ L f) (x : E) :
    HasGradientAt (shiftedObjective μ f) (shiftedGradient μ f x) x := by
  -- Subtract the quadratic-gradient formula from the ambient gradient of `f`.
  have hsub :
      HasFDerivAt (fun u : E ↦ f u - (μ / 2) * ‖u‖ ^ (2 : ℕ))
        ((InnerProductSpace.toDual ℝ E) (∇ f x) -
          (InnerProductSpace.toDual ℝ E) (μ • x)) x := by
    simpa using
      (hf.contDiff.differentiable_one x |>.hasGradientAt).hasFDerivAt.sub
        (shiftedQuadratic_hasFDerivAt μ x)
  have hdual :
      ((InnerProductSpace.toDual ℝ E) (∇ f x) -
          (InnerProductSpace.toDual ℝ E) (μ • x)) =
        InnerProductSpace.toDual ℝ E (∇ f x - μ • x) := by
    ext u
    simp [InnerProductSpace.toDual_apply_apply]
  have hgrad0 :
      HasGradientAt (fun u : E ↦ f u - (μ / 2) * ‖u‖ ^ (2 : ℕ)) (∇ f x - μ • x) x := by
    have hgrad1 := (hdual ▸ hsub).hasGradientAt
    have hsymm :
        (InnerProductSpace.toDual ℝ E).symm
            ((InnerProductSpace.toDual ℝ E) (∇ f x - μ • x)) =
          (∇ f x - μ • x) := by
      simp
    rw [hsymm] at hgrad1
    exact hgrad1
  simpa [shiftedObjective, shiftedGradient] using hgrad0

/-- Helper for Theorem 2.13: subtracting `(μ / 2) * ‖·‖²` turns the objective into a convex
function. -/
private theorem shiftedObjective_convex
    (hf : IsStrongConvexSmoothObjective μ L f) :
    ConvexOn ℝ Set.univ (shiftedObjective μ f) := by
  -- Rewrite strong convexity of `f` as ordinary convexity of the shifted objective.
  simpa [shiftedObjective] using (strongConvexOn_iff_convex.mp hf.strongConvexOn)

/-- Helper for Theorem 2.13: the shifted objective has the upper tangent model with curvature
`L - μ`. -/
private theorem shiftedObjective_upperTangentQuadratic
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    shiftedObjective μ f y ≤
      shiftedObjective μ f x +
        inner ℝ (shiftedGradient μ f x) (y - x) +
        ((L - μ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Start from the owner upper tangent bound for `f`.
  have hupper := hf.upper_tangent_quadratic x y
  -- Expand the quadratic shift along the displacement `y - x`.
  have hquad :
      (μ / 2) * ‖y‖ ^ (2 : ℕ) =
        (μ / 2) * ‖x‖ ^ (2 : ℕ) +
          μ * inner ℝ x (y - x) +
          (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    calc
      (μ / 2) * ‖y‖ ^ (2 : ℕ)
          = (μ / 2) * ‖x + (y - x)‖ ^ (2 : ℕ) := by congr 1; abel
      _ = (μ / 2) * (‖x‖ ^ (2 : ℕ) + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ (2 : ℕ)) := by
            rw [norm_add_sq_real]
      _ = (μ / 2) * ‖x‖ ^ (2 : ℕ) +
            μ * inner ℝ x (y - x) +
            (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
            ring
  -- Move the quadratic correction to the left-hand side and simplify.
  have hrewrite :
      shiftedObjective μ f y =
        shiftedObjective μ f x +
          (f y - f x) -
          μ * inner ℝ x (y - x) -
          (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    dsimp [shiftedObjective]
    rw [hquad]
    ring
  have hleft :
      shiftedObjective μ f x +
          inner ℝ (shiftedGradient μ f x) (y - x) +
          ((L - μ) / 2) * ‖y - x‖ ^ (2 : ℕ) =
        shiftedObjective μ f x +
          inner ℝ (∇ f x) (y - x) -
          μ * inner ℝ x (y - x) -
          (μ / 2) * ‖y - x‖ ^ (2 : ℕ) +
          (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    dsimp [shiftedGradient]
    rw [inner_sub_left, real_inner_smul_left]
    ring
  rw [hrewrite, hleft]
  linarith [hupper]

/-- Helper for Theorem 2.13: the shifted objective satisfies the quadratic lower gradient bound
with constant `L - μ`. -/
private theorem shiftedObjective_gradientQuadraticLowerBound
    (hf : IsStrongConvexSmoothObjective μ L f) (hδ : 0 < L - μ) (x y : E) :
    shiftedObjective μ f x +
        inner ℝ (shiftedGradient μ f x) (y - x) +
        (1 / (2 * (L - μ))) *
          ‖shiftedGradient μ f x - shiftedGradient μ f y‖ ^ (2 : ℕ) ≤
      shiftedObjective μ f y := by
  let φ : E → ℝ := fun z ↦ shiftedObjective μ f z - inner ℝ (shiftedGradient μ f x) z
  let gy : E := shiftedGradient μ f y - shiftedGradient μ f x
  let α : ℝ := 1 / (L - μ)
  let d : E := -(α • gy)
  let a : ℝ := ‖shiftedGradient μ f x - shiftedGradient μ f y‖ ^ (2 : ℕ)
  -- Convexity makes `x` a minimizer of the translated shifted objective.
  have hx_min : ∀ z : E, φ x ≤ φ z := by
    intro z
    have hderivAt :
        HasFDerivAt (shiftedObjective μ f)
          ((InnerProductSpace.toDual ℝ E) (shiftedGradient μ f x)) x := by
      simpa [shiftedGradient] using
        (shiftedObjective_hasGradientAt hf x).hasFDerivAt
    have hgradWithin :
        HasGradientWithinAt (shiftedObjective μ f) (shiftedGradient μ f x) Set.univ x :=
      by
        exact (hasGradientWithinAt_iff_hasFDerivWithinAt).2 hderivAt.hasFDerivWithinAt
    have hsupport :=
      (shiftedObjective_convex hf).lower_tangent_plane_of_hasGradientWithinAt
        x (by simp) (shiftedGradient μ f x) hgradWithin z (by simp)
    have hphi_nonneg : 0 ≤ φ z - φ x := by
      have hphi_eq :
          φ z - φ x =
            shiftedObjective μ f z - shiftedObjective μ f x -
              inner ℝ (shiftedGradient μ f x) (z - x) := by
        dsimp [φ]
        rw [inner_sub_right]
        ring_nf
      rw [hphi_eq]
      linarith
    linarith
  -- The explicit descent direction optimizes the quadratic upper model exactly.
  have hα_pos : 0 < α := by
    dsimp [α]
    exact one_div_pos.mpr hδ
  have hnorm_gy :
      ‖gy‖ ^ (2 : ℕ) = a := by
    dsimp [gy, a]
    rw [show shiftedGradient μ f y - shiftedGradient μ f x =
      -(shiftedGradient μ f x - shiftedGradient μ f y) by abel]
    rw [norm_neg]
  have hinner_d :
      inner ℝ gy d = -α * ‖gy‖ ^ (2 : ℕ) := by
    dsimp [d]
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm_d :
      ‖d‖ ^ (2 : ℕ) = α ^ (2 : ℕ) * ‖gy‖ ^ (2 : ℕ) := by
    dsimp [d]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα_pos.le, mul_pow]
  have hd_eq :
      inner ℝ gy d + ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) =
        -(1 / (2 * (L - μ))) * a := by
    rw [hinner_d, hnorm_d, hnorm_gy]
    dsimp [α]
    field_simp [hδ.ne']
    ring
  have hd' :
      inner ℝ gy d + ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) ≤
        -(1 / (2 * (L - μ))) * a := by
    rw [hd_eq]
  -- Apply the shifted upper tangent model at `y` and the minimizing property at `x`.
  have hup :
      φ (y + d) ≤
        φ y + inner ℝ gy d + ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    have hy' := shiftedObjective_upperTangentQuadratic hf y (y + d)
    have hy'' :
        shiftedObjective μ f (y + d) - shiftedObjective μ f y -
            inner ℝ (shiftedGradient μ f y) d ≤
          ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      have hsub : y + d - y = d := by
        abel_nf
      have hy''':
          shiftedObjective μ f (y + d) ≤
            shiftedObjective μ f y +
              inner ℝ (shiftedGradient μ f y) d +
              ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) := by
        rw [hsub] at hy'
        simpa using hy'
      linarith
    have hphi_upper :
        φ (y + d) - φ y - inner ℝ gy d ≤
          ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      have hgy_d :
          inner ℝ (shiftedGradient μ f x) d + inner ℝ gy d =
            inner ℝ (shiftedGradient μ f y) d := by
        dsimp [gy, shiftedGradient]
        rw [inner_sub_left, inner_sub_left, inner_sub_left, inner_sub_left]
        ring
      have hphi_eq :
          φ (y + d) - φ y - inner ℝ gy d =
            shiftedObjective μ f (y + d) - shiftedObjective μ f y -
              inner ℝ (shiftedGradient μ f y) d := by
        calc
          φ (y + d) - φ y - inner ℝ gy d =
              shiftedObjective μ f (y + d) -
                inner ℝ (shiftedGradient μ f x) (y + d) -
                (shiftedObjective μ f y - inner ℝ (shiftedGradient μ f x) y) -
                inner ℝ gy d := by
                  rfl
          _ = shiftedObjective μ f (y + d) -
                inner ℝ (shiftedGradient μ f x) y -
                inner ℝ (shiftedGradient μ f x) d -
                (shiftedObjective μ f y - inner ℝ (shiftedGradient μ f x) y) -
                inner ℝ gy d := by
                  rw [inner_add_right]
                  ring
          _ = shiftedObjective μ f (y + d) - shiftedObjective μ f y -
                inner ℝ (shiftedGradient μ f x) d - inner ℝ gy d := by
                ring
          _ = shiftedObjective μ f (y + d) - shiftedObjective μ f y -
                inner ℝ (shiftedGradient μ f y) d := by
                linarith [hgy_d]
      rw [hphi_eq]
      exact hy''
    linarith
  -- Comparing the minimizer `x` against the explicit trial point yields the lower bound.
  have hphi :
      φ x ≤ φ y - (1 / (2 * (L - μ))) * a := by
    calc
      φ x ≤ φ (y + d) := hx_min (y + d)
      _ ≤ φ y + inner ℝ gy d + ((L - μ) / 2) * ‖d‖ ^ (2 : ℕ) := hup
      _ ≤ φ y - (1 / (2 * (L - μ))) * a := by
            linarith
  have hfinal :
      shiftedObjective μ f x +
          inner ℝ (shiftedGradient μ f x) (y - x) +
          (1 / (2 * (L - μ))) * a ≤
        shiftedObjective μ f y := by
    have hphi' :
        shiftedObjective μ f x -
            inner ℝ (shiftedGradient μ f x) x +
            (1 / (2 * (L - μ))) * a ≤
          shiftedObjective μ f y -
            inner ℝ (shiftedGradient μ f x) y := by
      dsimp [φ] at hphi
      linarith
    have hrewrite :
        shiftedObjective μ f x +
            inner ℝ (shiftedGradient μ f x) (y - x) +
            (1 / (2 * (L - μ))) * a =
          shiftedObjective μ f x -
            inner ℝ (shiftedGradient μ f x) x +
            (1 / (2 * (L - μ))) * a +
            inner ℝ (shiftedGradient μ f x) y := by
      rw [inner_sub_right]
      ring
    rw [hrewrite]
    linarith
  simpa [a] using hfinal

/-- Helper for Theorem 2.13: the shifted gradient field is `1 / (L - μ)`-cocoercive when
`μ < L`. -/
private theorem shiftedObjective_cocoercivePairing
    (hf : IsStrongConvexSmoothObjective μ L f) (hδ : 0 < L - μ) (x y : E) :
    (1 / (L - μ)) * ‖shiftedGradient μ f x - shiftedGradient μ f y‖ ^ (2 : ℕ) ≤
      inner ℝ (shiftedGradient μ f x - shiftedGradient μ f y) (x - y) := by
  -- Add the quadratic lower bound in both endpoint orders.
  have hxy := shiftedObjective_gradientQuadraticLowerBound hf hδ x y
  have hyx := shiftedObjective_gradientQuadraticLowerBound hf hδ y x
  let a : ℝ := ‖shiftedGradient μ f x - shiftedGradient μ f y‖ ^ (2 : ℕ)
  have hnorm :
      ‖shiftedGradient μ f y - shiftedGradient μ f x‖ ^ (2 : ℕ) = a := by
    dsimp [a]
    rw [show shiftedGradient μ f y - shiftedGradient μ f x =
      -(shiftedGradient μ f x - shiftedGradient μ f y) by abel]
    rw [norm_neg]
  have hxy' :
      shiftedObjective μ f x +
          inner ℝ (shiftedGradient μ f x) (y - x) +
          (1 / (2 * (L - μ))) * a ≤
        shiftedObjective μ f y := by
    simpa [a] using hxy
  have hyx' :
      shiftedObjective μ f y +
          inner ℝ (shiftedGradient μ f y) (x - y) +
          (1 / (2 * (L - μ))) * a ≤
        shiftedObjective μ f x := by
    rw [hnorm] at hyx
    simpa [a] using hyx
  have hlin :
      inner ℝ (shiftedGradient μ f x) (y - x) +
          inner ℝ (shiftedGradient μ f y) (x - y) =
        -inner ℝ (shiftedGradient μ f x - shiftedGradient μ f y) (x - y) := by
    dsimp [shiftedGradient]
    rw [show y - x = -(x - y) by abel, inner_neg_right, inner_sub_left, inner_sub_left,
      inner_sub_left, inner_sub_left, inner_sub_left]
    ring
  have hpairing0 :
      inner ℝ (shiftedGradient μ f x) (y - x) +
          inner ℝ (shiftedGradient μ f y) (x - y) +
          (1 / (L - μ)) * a ≤ 0 := by
    have hxy'' :
        inner ℝ (shiftedGradient μ f x) (y - x) +
            (1 / (2 * (L - μ))) * a ≤
          shiftedObjective μ f y - shiftedObjective μ f x := by
      linarith [hxy']
    have hyx'' :
        inner ℝ (shiftedGradient μ f y) (x - y) +
            (1 / (2 * (L - μ))) * a ≤
          shiftedObjective μ f x - shiftedObjective μ f y := by
      linarith [hyx']
    have hsum0 := add_le_add hxy'' hyx''
    have hsumAux :
        inner ℝ (shiftedGradient μ f x) (y - x) +
            (1 / (2 * (L - μ))) * a +
            (inner ℝ (shiftedGradient μ f y) (x - y) +
              (1 / (2 * (L - μ))) * a) ≤ 0 := by
      have hrhs :
          shiftedObjective μ f y - shiftedObjective μ f x +
              (shiftedObjective μ f x - shiftedObjective μ f y) = 0 := by
        ring
      rw [hrhs] at hsum0
      exact hsum0
    have hsum1 :
        inner ℝ (shiftedGradient μ f x) (y - x) +
            inner ℝ (shiftedGradient μ f y) (x - y) +
            (1 / (L - μ)) * a ≤ 0 := by
      have haux := hsumAux
      have hcoef : (L * 2 - μ * 2)⁻¹ * a * 2 = a * (L - μ)⁻¹ := by
        field_simp [hδ.ne']
      ring_nf at haux ⊢
      rw [hcoef] at haux
      exact haux
    exact hsum1
  have hpairing :
      inner ℝ (shiftedGradient μ f x) (y - x) +
          inner ℝ (shiftedGradient μ f y) (x - y) ≤
        -(1 / (L - μ)) * a := by
    linarith [hpairing0]
  rw [hlin] at hpairing
  simpa [a] using (show (1 / (L - μ)) * a ≤
    inner ℝ (shiftedGradient μ f x - shiftedGradient μ f y) (x - y) by
      nlinarith [hpairing, hδ])

/- Theorem 2.13 is stated in the text on `ℝⁿ`; the owner theorem below records the same statement
for the ambient real Hilbert-space abstraction, and hence specializes back to the Euclidean case.
The parameter relation `μ ≤ L` is not kept as primitive public data: on nontrivial spaces it is a
derived consequence of `hf`, while on subsingleton spaces the displayed inequality is trivial. -/
/-- Theorem 2.13: a function in `𝓢^{1,1}_{μ,L}` satisfies the strengthened secant inequality
`⟪∇ f x - ∇ f y, x - y⟫ ≥ (μ L / (μ + L)) ‖x - y‖² + (1 / (μ + L)) ‖∇ f x - ∇ f y‖²`
for all `x, y`. -/
-- Proof sketch: use the owner theorem `hf.gradient_strong_mono` together with the gradient
-- Lipschitz bound, apply
-- the same owner-side secant argument to the shifted objective `z ↦ f z - (μ / 2) * ‖z‖²`, and
-- rearrange the resulting
-- inequality. The endpoint case `μ = L` gives equality.
theorem pairing_lower_bound
    (hf : IsStrongConvexSmoothObjective μ L f)
    (x y : E) :
    inner ℝ (∇ f x - ∇ f y) (x - y) ≥
      (μ * L / (μ + L)) * ‖x - y‖ ^ 2 +
        (1 / (μ + L)) * ‖∇ f x - ∇ f y‖ ^ 2 := by
  by_cases hE : Subsingleton E
  · -- In the degenerate ambient space every pair of points coincides, so the claim is trivial.
    have hxy : x = y := hE.elim x y
    subst hxy
    simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hμL : μ ≤ L := hf.mu_le_L
    have hsum_pos : 0 < μ + L := by
      nlinarith [hf.mu_pos, hμL]
    by_cases hEq : μ = L
    · -- Endpoint branch: combine strong monotonicity with the `μ`-Lipschitz gradient bound.
      subst hEq
      let d : E := x - y
      let Δ : E := ∇ f x - ∇ f y
      have hmono : μ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ Δ d := by
        simpa [d, Δ] using hf.gradient_strong_mono x y
      have hlip : ‖Δ‖ ≤ μ * ‖d‖ := by
        simpa [d, Δ] using hf.gradient_lipschitz x y
      have hnorm_sq : ‖Δ‖ ^ (2 : ℕ) ≤ μ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
        nlinarith [hlip, norm_nonneg Δ, norm_nonneg d]
      have hhalf :
          (1 / (μ + μ)) * ‖Δ‖ ^ (2 : ℕ) ≤ (μ / 2) * ‖d‖ ^ (2 : ℕ) := by
        calc
          (1 / (μ + μ)) * ‖Δ‖ ^ (2 : ℕ) ≤
              (1 / (μ + μ)) * (μ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ)) := by
                have hcoef_nonneg : 0 ≤ 1 / (μ + μ) := by positivity
                exact mul_le_mul_of_nonneg_left hnorm_sq hcoef_nonneg
          _ = (μ / 2) * ‖d‖ ^ (2 : ℕ) := by
                field_simp [show μ + μ ≠ 0 by positivity]
                ring
      have hrhs :
          (μ * μ / (μ + μ)) * ‖d‖ ^ (2 : ℕ) +
              (1 / (μ + μ)) * ‖Δ‖ ^ (2 : ℕ) ≤
            μ * ‖d‖ ^ (2 : ℕ) := by
        have hcoef :
            (μ * μ / (μ + μ)) * ‖d‖ ^ (2 : ℕ) = (μ / 2) * ‖d‖ ^ (2 : ℕ) := by
          field_simp [show μ + μ ≠ 0 by positivity]
          ring
        rw [hcoef]
        linarith
      have htarget :
          (μ * μ / (μ + μ)) * ‖d‖ ^ (2 : ℕ) +
              (1 / (μ + μ)) * ‖Δ‖ ^ (2 : ℕ) ≤
            inner ℝ Δ d := by
        exact hrhs.trans hmono
      simpa [d, Δ] using htarget
    · -- Strict branch: apply cocoercivity to the shifted gradient and expand back.
      have hδ : 0 < L - μ := sub_pos.mpr (lt_of_le_of_ne hμL hEq)
      let d : E := x - y
      let Δ : E := ∇ f x - ∇ f y
      have hshift := shiftedObjective_cocoercivePairing hf hδ x y
      have hgdiff :
          shiftedGradient μ f x - shiftedGradient μ f y = Δ - μ • d := by
        dsimp [shiftedGradient, Δ, d]
        rw [smul_sub]
        abel_nf
      rw [hgdiff] at hshift
      have hshift' :
          (1 / (L - μ)) * ‖Δ - μ • d‖ ^ (2 : ℕ) ≤
            inner ℝ (Δ - μ • d) d := by
        simpa [d] using hshift
      have hpair :
          inner ℝ (Δ - μ • d) d = inner ℝ Δ d - μ * ‖d‖ ^ (2 : ℕ) := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      have hnorm :
          ‖Δ - μ • d‖ ^ (2 : ℕ) =
            ‖Δ‖ ^ (2 : ℕ) - 2 * μ * inner ℝ Δ d + μ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
        rw [norm_sub_sq_real, real_inner_smul_right,
          norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      have htarget :
          (μ * L / (μ + L)) * ‖d‖ ^ (2 : ℕ) +
              (1 / (μ + L)) * ‖Δ‖ ^ (2 : ℕ) ≤
            inner ℝ Δ d := by
        have hscaled0 :
            ‖Δ - μ • d‖ ^ (2 : ℕ) ≤
              (L - μ) * inner ℝ (Δ - μ • d) d := by
          have hquot :
              ‖Δ - μ • d‖ ^ (2 : ℕ) / (L - μ) ≤
                inner ℝ (Δ - μ • d) d := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hshift'
          simpa [mul_comm] using (div_le_iff₀ hδ).1 hquot
        have hscaled :
            ‖Δ‖ ^ (2 : ℕ) - 2 * μ * inner ℝ Δ d + μ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) ≤
              (L - μ) * (inner ℝ Δ d - μ * ‖d‖ ^ (2 : ℕ)) := by
          rw [hnorm, hpair] at hscaled0
          exact hscaled0
        have hnumerator :
            ‖Δ‖ ^ (2 : ℕ) + μ * L * ‖d‖ ^ (2 : ℕ) ≤
              (μ + L) * inner ℝ Δ d := by
          nlinarith [hscaled]
        have hdiv :
            (‖Δ‖ ^ (2 : ℕ) + μ * L * ‖d‖ ^ (2 : ℕ)) / (μ + L) ≤
              inner ℝ Δ d := by
          exact (div_le_iff₀ hsum_pos).2 (by simpa [mul_comm] using hnumerator)
        have hrew :
            (μ * L / (μ + L)) * ‖d‖ ^ (2 : ℕ) +
                (1 / (μ + L)) * ‖Δ‖ ^ (2 : ℕ) =
              (‖Δ‖ ^ (2 : ℕ) + μ * L * ‖d‖ ^ (2 : ℕ)) / (μ + L) := by
          field_simp [show μ + L ≠ 0 by positivity]
          ring
        rw [hrew]
        exact hdiv
      simpa [d, Δ] using htarget

end IsStrongConvexSmoothObjective
