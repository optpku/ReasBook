/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_22
import FirstOrderMethodsOptimization_Beck_2017.Chap05.ConjugateFunctionStrongDual
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_5
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import Mathlib.Analysis.Convex.Deriv

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ} {p : ℝ}

local notation "E" => WithLp (ENNReal.ofReal p) (Fin n → ℝ)

private theorem one_le_ofReal_of_one_lt (hp : 1 < p) : 1 ≤ ENNReal.ofReal p := by
  exact (ENNReal.one_le_ofReal).2 (by linarith)

private theorem factOneLeOfRealOfOneLt (hp : 1 < p) :
    Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨one_le_ofReal_of_one_lt hp⟩

private instance factOneLeOfRealOfFactOneLt [Fact (1 < p)] :
    Fact (1 ≤ ENNReal.ofReal p) :=
  factOneLeOfRealOfOneLt ‹Fact (1 < p)›.1

/-- Helper for Proposition 5.15: the half-squared `ℓ_p` norm is convex on the canonical `WithLp`
model. -/
private theorem halfSquaredLpNorm_convexOn_univ [Fact (1 ≤ ENNReal.ofReal p)] :
    ConvexOn ℝ Set.univ (halfSquaredLpNorm n p) := by
  -- Rewrite the function as a positive scalar multiple of the convex norm-square map.
  have hnormSq : ConvexOn ℝ Set.univ (fun z : E ↦ ‖z‖ ^ (2 : ℕ)) :=
    convexOn_univ_norm.pow (fun z _ ↦ norm_nonneg z) 2
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hsq :
      ‖a • x + b • y‖ ^ (2 : ℕ) ≤ a * ‖x‖ ^ (2 : ℕ) + b * ‖y‖ ^ (2 : ℕ) := by
    simpa [smul_eq_mul] using hnormSq.2 (x := x) (by simp) (y := y) (by simp) ha hb hab
  have hscaled :
      (1 / 2 : ℝ) * ‖a • x + b • y‖ ^ (2 : ℕ) ≤
        a * ((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) + b * ((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ)) := by
    nlinarith
  simpa [halfSquaredLpNorm, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
    hscaled

/-- Helper for Proposition 5.15: the displacement from a barycenter to its first endpoint is the
expected scalar multiple of the chord. -/
private theorem barycenterDisplacement_eq_smul_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (hab : a + b = 1) (x y : F) :
    x - (a • x + b • y) = b • (x - y) ∧
      y - (a • x + b • y) = a • (y - x) := by
  constructor
  · -- Normalize the first displacement by rewriting the second barycentric coefficient as `1 - a`.
    have hb : b = 1 - a := by
      linarith
    rw [hb]
    module
  · -- Normalize the second displacement symmetrically by rewriting the first coefficient.
    have ha : a = 1 - b := by
      linarith
    rw [ha]
    module

/-- Helper for Proposition 5.15: the weighted quadratic remainder at a barycenter collapses to the
standard `a * b` chord factor. -/
private theorem weightedBarycenterChordNormSq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x y : F) :
    a * ‖x - (a • x + b • y)‖ ^ (2 : ℕ) + b * ‖y - (a • x + b • y)‖ ^ (2 : ℕ) =
      a * b * ‖x - y‖ ^ (2 : ℕ) := by
  -- First rewrite both endpoint displacements into scalar multiples of the same chord.
  obtain ⟨hx, hy⟩ := barycenterDisplacement_eq_smul_sub hab x y
  rw [hx, hy, norm_smul, norm_smul]
  simp only [pow_two, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, norm_sub_rev]
  -- Then collect the scalar coefficients into the expected `a * b` factor.
  have hab' : a * b * b + a * a * b = a * b := by
    calc
      a * b * b + a * a * b = a * b * (a + b) := by
        ring
      _ = a * b := by
        rw [hab, mul_one]
  calc
    a * (b * ‖x - y‖ * (b * ‖x - y‖)) + b * (a * ‖x - y‖ * (a * ‖x - y‖)) =
        (a * b * b + a * a * b) * (‖x - y‖ * ‖x - y‖) := by
          ring
    _ = a * b * (‖x - y‖ * ‖x - y‖) := by
          rw [hab']

/-- Helper for Proposition 5.15: the weighted first-order support term at a barycenter cancels in
the exact scalar normal form produced by linearity. -/
private theorem weightedSupportDifference_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (hab : a + b = 1) (gz : StrongDual ℝ F) (x y : F) :
    a * (gz x - gz (a • x + b • y)) + b * (gz y - gz (a • x + b • y)) = 0 := by
  -- Expand the barycenter evaluation once and then collect the scalar coefficients.
  have hgz :
      gz (a • x + b • y) = a * gz x + b * gz y := by
    simp [map_add, map_smul, smul_eq_mul]
  calc
    a * (gz x - gz (a • x + b • y)) + b * (gz y - gz (a • x + b • y)) =
        a * gz x + b * gz y - (a + b) * gz (a • x + b • y) := by
          ring
    _ = a * gz x + b * gz y - gz (a • x + b • y) := by rw [hab, one_mul]
    _ = 0 := by rw [hgz, sub_self]

/-- Helper for Proposition 5.15: a global quadratic lower-support family yields the canonical
owner statement `StrongConvexOn Set.univ σ f`. -/
private theorem strongConvexOn_univ_of_supportLowerBound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {σ : ℝ} {f : F → ℝ}
    (hsupport :
      ∀ x : F, ∃ gx : StrongDual ℝ F, ∀ y : F,
        f y ≥ f x + gx (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ)) :
    StrongConvexOn Set.univ σ f := by
  -- Route correction: the remaining seam is purely a normal-form package. Evaluate the support
  -- family at `z = a • x + b • y`, cancel the support term via
  -- `a • (x - z) + b • (y - z) = 0`, and finish with
  -- `barycenterDisplacement_eq_smul_sub` and `weightedBarycenterChordNormSq`.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z : F := a • x + b • y
  obtain ⟨gz, hgz⟩ := hsupport z
  have hx :
      a * (f z + gz (x - z) + (σ / 2) * ‖x - z‖ ^ (2 : ℕ)) ≤ a * f x := by
    exact mul_le_mul_of_nonneg_left (hgz x) ha
  have hy :
      b * (f z + gz (y - z) + (σ / 2) * ‖y - z‖ ^ (2 : ℕ)) ≤ b * f y := by
    exact mul_le_mul_of_nonneg_left (hgz y) hb
  have hsum :
      a * (f z + gz (x - z) + (σ / 2) * ‖x - z‖ ^ (2 : ℕ)) +
          b * (f z + gz (y - z) + (σ / 2) * ‖y - z‖ ^ (2 : ℕ)) ≤
        a * f x + b * f y := by
    exact add_le_add hx hy
  have hcancel :
      a * gz (x - z) + b * gz (y - z) = 0 := by
    -- Rewrite the two support evaluations into the exact scalar-output normal form handled above.
    simpa [z, map_sub, smul_eq_mul, mul_add, add_mul, sub_eq_add_neg,
      mul_assoc, mul_left_comm, mul_comm] using
      weightedSupportDifference_eq_zero hab gz x y
  have hquad :
      a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ) = a * b * ‖x - y‖ ^ (2 : ℕ) := by
    simpa [z] using weightedBarycenterChordNormSq ha hb hab x y
  have hpack :
      a * (f z + gz (x - z) + (σ / 2) * ‖x - z‖ ^ (2 : ℕ)) +
          b * (f z + gz (y - z) + (σ / 2) * ‖y - z‖ ^ (2 : ℕ)) =
        f z + (σ / 2) * (a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ)) := by
    calc
      a * (f z + gz (x - z) + (σ / 2) * ‖x - z‖ ^ (2 : ℕ)) +
          b * (f z + gz (y - z) + (σ / 2) * ‖y - z‖ ^ (2 : ℕ)) =
          a * f z + b * f z + (a * gz (x - z) + b * gz (y - z)) +
            (σ / 2) * (a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ)) := by
              ring
      _ = a * f z + b * f z + (σ / 2) * (a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ)) := by
            rw [hcancel, add_zero]
      _ = (a + b) * f z + (σ / 2) * (a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ)) := by
            ring
      _ = f z + (σ / 2) * (a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ)) := by
            rw [hab, one_mul]
  have hmain :
      f z + (σ / 2) * (a * ‖x - z‖ ^ (2 : ℕ) + b * ‖y - z‖ ^ (2 : ℕ)) ≤
        a * f x + b * f y := by
    rw [← hpack]
    exact hsum
  have htarget :
      f z ≤ a * f x + b * f y - a * b * ((σ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
    rw [hquad] at hmain
    nlinarith
  simpa [StrongConvexOn, z, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using htarget

/-- Helper for Proposition 5.15: strong convexity pulls back along a linear isometry of normed
spaces. -/
private theorem strongConvexOn_comp_of_normPreservingLinearMap
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {σ : ℝ} {g : G → ℝ} (A : F →ₗ[ℝ] G)
    (hA : ∀ z : F, ‖A z‖ = ‖z‖)
    (hg : StrongConvexOn Set.univ σ g) :
    StrongConvexOn Set.univ σ (fun x : F ↦ g (A x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Apply strong convexity on the image points and then rewrite the barycenter/chord by linearity.
  have hmain :=
    hg.2 (show A x ∈ Set.univ by simp) (show A y ∈ Set.univ by simp) ha hb hab
  have hnorm : ‖A x - A y‖ = ‖x - y‖ := by
    rw [← map_sub, hA (x - y)]
  simpa [smul_eq_mul, map_add, map_smul, hnorm, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Helper for Proposition 5.15: evaluating the Fenchel conjugate of the q-side half-squared
`ℓ_q` norm at the canonical `ℓ_q/ℓ_p` pairing functional recovers the p-side half-squared
`ℓ_p` norm. -/
private theorem conjugateHalfSquaredLpNorm_applyLpPairingDual
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (_hp₂ : p ≤ 2) (x : E) :
    let q : ℝ := (ENNReal.conjExponent (ENNReal.ofReal p)).toReal
    conjugate_function
      (fun z : WithLp (ENNReal.ofReal q) (Fin n → ℝ) ↦
        ((((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)) : ℝ) : EReal))
      (lpPairingDual (ENNReal.ofReal q) (WithLp.ofLp x)) =
        ((halfSquaredLpNorm n p x : ℝ) : EReal) := by
  -- Route correction: apply Proposition 4.22 on the `q`-side owner first, then rewrite the dual
  -- norm of the canonical pairing functional with Proposition 1.9 and `WithLp.toLp_ofLp`.
  let q : ℝ := (ENNReal.conjExponent (ENNReal.ofReal p)).toReal
  have hpPos : 0 < p := lt_trans zero_lt_one hp
  have hpqReal : p.HolderConjugate q := by
    simpa [q, ENNReal.toReal_ofReal hpPos.le] using
      (ENNReal.HolderConjugate.toReal
        (p := ENNReal.ofReal p)
        (q := ENNReal.conjExponent (ENNReal.ofReal p))
        (by simpa [ENNReal.toReal_ofReal hpPos.le] using hp))
  have hpqENN : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    hpqReal.ennrealOfReal
  letI : Fact (1 ≤ ENNReal.ofReal q) := ENNReal.HolderConjugate.factOneLeRight hpqENN
  let yq : Module.Dual ℝ (WithLp (ENNReal.ofReal q) (Fin n → ℝ)) :=
    lpPairingDual (ENNReal.ofReal q) (WithLp.ofLp x)
  have hconj :
      conjugate_function
          (fun z : WithLp (ENNReal.ofReal q) (Fin n → ℝ) ↦
            ((((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)) : ℝ) : EReal))
          yq =
        ((((1 / 2 : ℝ) * dualNorm yq ^ (2 : ℕ)) : ℝ) : EReal) := by
    -- Apply the Chapter 4 quadratic conjugate formula on the exact `q`-side owner first.
    simpa [yq] using (half_squared_norm_conjugate_eq_half_dualNorm_sq (y := yq))
  have hdual :
      dualNorm yq = ‖x‖ := by
    -- Rewrite the pairing norm through the canonical conjugate exponent, then identify that
    -- exponent with `p` using the Hölder-conjugate instance on `q`.
    letI : ENNReal.HolderConjugate (ENNReal.ofReal q) (ENNReal.ofReal p) := hpqENN.symm
    calc
      dualNorm yq =
          ‖WithLp.toLp (ENNReal.conjExponent (ENNReal.ofReal q)) (WithLp.ofLp x)‖ := by
            simpa [yq] using
              (dualNorm_lpPairingDual_eq_conjExponent_lp_norm
                (p := ENNReal.ofReal q) (y := WithLp.ofLp x))
      _ = ‖WithLp.toLp (ENNReal.ofReal p) (WithLp.ofLp x)‖ := by
            rw [ENNReal.HolderConjugate.conjExponent_eq (p := ENNReal.ofReal q)
              (q := ENNReal.ofReal p)]
      _ = ‖x‖ := by simp
  calc
    conjugate_function
        (fun z : WithLp (ENNReal.ofReal q) (Fin n → ℝ) ↦
          ((((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)) : ℝ) : EReal))
        (lpPairingDual (ENNReal.ofReal q) (WithLp.ofLp x)) =
        ((((1 / 2 : ℝ) * dualNorm yq ^ (2 : ℕ)) : ℝ) : EReal) := by
          simpa [yq] using hconj
    _ = ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
          rw [hdual]
    _ = ((halfSquaredLpNorm n p x : ℝ) : EReal) := by
          congr 1
          rw [halfSquaredLpNorm]
          ring

/- Proposition 5.15 is `source-facing`: the textbook object is the half-squared `ℓ_p` norm on
`ℝ^n` for `1 < p ≤ 2`. Domain sampling points to mathlib's owner predicate `StrongConvexOn` and
the canonical `WithLp` model of `ℝ^n`; the chapter's extended-real-valued predicate from
Definition 5.16 is the derived bridge/view rather than the owner-level main statement. -/

/-- Helper for Proposition 5.15: on the Hölder-conjugate `q` side, the continuous-dual Fenchel
conjugate of `halfSquaredLpNorm n q` is globally `(p - 1)`-strongly convex. -/
private theorem qSideConjugateStrongConvexOn
    (n : ℕ) {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hp_sub_pos : 0 < p - 1)
    (hsmooth : is_l_smooth_on (halfSquaredLpNorm n q) Set.univ (Real.toNNReal (1 / (p - 1)))) :
    StrongConvexOn Set.univ (p - 1)
      (fun η : StrongDual ℝ (WithLp (ENNReal.ofReal q) (Fin n → ℝ)) ↦
        (conjugate_function_strongDual (halfSquaredLpNorm n q).toEReal η).toReal) := by
  let G : Type := WithLp (ENNReal.ofReal q) (Fin n → ℝ)
  let h : StrongDual ℝ G → ℝ := fun η ↦
    (conjugate_function_strongDual (halfSquaredLpNorm n q).toEReal η).toReal
  have hdom :
      effective_domain (conjugate_function_strongDual (halfSquaredLpNorm n q).toEReal) = Set.univ := by
    ext η
    constructor
    · intro hη
      simp
    · intro hη
      refine mem_effective_domain.mpr ?_
      have hhalf :
          (halfSquaredLpNorm n q).toEReal =
            (fun x : G ↦ ((((1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
        funext x
        simp [halfSquaredLpNorm, Function.toEReal, div_eq_mul_inv, mul_comm]
      have hconj :
          conjugate_function_strongDual (halfSquaredLpNorm n q).toEReal η =
            ((((1 / 2 : ℝ) *
                dualNorm ((η : StrongDual ℝ G) : Module.Dual ℝ G) ^ (2 : ℕ)) : ℝ) : EReal) := by
        rw [hhalf]
        simpa using
          (half_squared_norm_conjugate_eq_half_dualNorm_sq
            (y := ((η : StrongDual ℝ G) : Module.Dual ℝ G)))
      rw [hconj]
      exact EReal.coe_lt_top _
  have hconvex : ConvexOn ℝ Set.univ (halfSquaredLpNorm n q) :=
    halfSquaredLpNorm_convexOn_univ (n := n) (p := q)
  simpa [h, hdom] using
    (strongConvexOn_toReal_conjugate_function_of_convex_is_l_smooth
      (σ := p - 1)
      hp_sub_pos
      (halfSquaredLpNorm n q)
      hconvex
      hsmooth)

/-- Helper for Proposition 5.15: the canonical pairing map from the `ℓ_p` model to the continuous
dual of the `ℓ_q` model is linear and norm preserving. -/
private def pairingStrongDualMap
    (n : ℕ) (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] :
    WithLp (ENNReal.ofReal p) (Fin n → ℝ) →ₗ[ℝ]
      StrongDual ℝ (WithLp (ENNReal.ofReal q) (Fin n → ℝ)) :=
  let G : Type := WithLp (ENNReal.ofReal q) (Fin n → ℝ)
  let A₀ : WithLp (ENNReal.ofReal p) (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ G :=
    { toFun := fun x ↦ lpPairingDual (ENNReal.ofReal q) (WithLp.ofLp x)
      map_add' := by
        intro x y
        ext z
        simp [lpPairingDual_apply, dotProduct, WithLp.ofLp_add, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro a x
        ext z
        simp [lpPairingDual_apply, dotProduct, WithLp.ofLp_smul, Finset.mul_sum,
          mul_assoc, mul_comm] }
  (LinearMap.toContinuousLinearMap : Module.Dual ℝ G ≃ₗ[ℝ] StrongDual ℝ G).toLinearMap.comp A₀

/-- Helper for Proposition 5.15: the canonical pairing map from the `ℓ_p` model to the continuous
dual of the `ℓ_q` model preserves the ambient norm. -/
private theorem pairingStrongDualMap_norm
    (n : ℕ) {p q : ℝ} (hpqENN : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q))
    [Fact (1 ≤ ENNReal.ofReal q)] (x : WithLp (ENNReal.ofReal p) (Fin n → ℝ)) :
    ‖pairingStrongDualMap n p q x‖ = ‖x‖ := by
  let G : Type := WithLp (ENNReal.ofReal q) (Fin n → ℝ)
  letI : ENNReal.HolderConjugate (ENNReal.ofReal q) (ENNReal.ofReal p) := hpqENN.symm
  calc
    ‖pairingStrongDualMap n p q x‖ =
        ‖LinearMap.toContinuousLinearMap (lpPairingDual (ENNReal.ofReal q) (WithLp.ofLp x))‖ := by
          rfl
    _ = dualNorm (lpPairingDual (ENNReal.ofReal q) (WithLp.ofLp x)) := by
          rw [← dualNorm_eq_toContinuousLinearMap_norm]
    _ = ‖WithLp.toLp (ENNReal.conjExponent (ENNReal.ofReal q)) (WithLp.ofLp x)‖ := by
          simpa using
            (dualNorm_lpPairingDual_eq_conjExponent_lp_norm
              (p := ENNReal.ofReal q) (y := WithLp.ofLp x))
    _ = ‖WithLp.toLp (ENNReal.ofReal p) (WithLp.ofLp x)‖ := by
          rw [ENNReal.HolderConjugate.conjExponent_eq (p := ENNReal.ofReal q)
            (q := ENNReal.ofReal p)]
    _ = ‖x‖ := by simp

namespace HalfSquaredLpNorm

/-- Canonical Chapter 5 owner theorem: for `1 < p ≤ 2`, the half-squared `ℓ_p` norm on the
canonical `WithLp` model is globally `(p - 1)`-strongly convex. -/
theorem isStronglyConvex [Fact (1 < p)] [Fact (p ≤ 2)] :
    StrongConvexOn Set.univ (p - 1) (halfSquaredLpNorm n p) := by
  let q : ℝ := (ENNReal.conjExponent (ENNReal.ofReal p)).toReal
  let hp : 1 < p := ‹Fact (1 < p)›.1
  let hp₂ : p ≤ 2 := ‹Fact (p ≤ 2)›.1
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_sub_pos : 0 < p - 1 := by linarith
  have hpqReal : p.HolderConjugate q := by
    simpa [q, ENNReal.toReal_ofReal hp_pos.le] using
      (ENNReal.HolderConjugate.toReal
        (p := ENNReal.ofReal p)
        (q := ENNReal.conjExponent (ENNReal.ofReal p))
        (by simpa [ENNReal.toReal_ofReal hp_pos.le] using hp))
  have hpqENN : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    hpqReal.ennrealOfReal
  letI : Fact (1 ≤ ENNReal.ofReal q) := ENNReal.HolderConjugate.factOneLeRight hpqENN
  have hq_eq : q = p / (p - 1) := by
    exact (Real.holderConjugate_iff_eq_conjExponent hp).mp hpqReal
  have hq_ge_two : 2 ≤ q := by
    rw [hq_eq]
    exact (le_div_iff₀ hp_sub_pos).2 (by linarith)
  have hq_sub : q - 1 = 1 / (p - 1) := by
    rw [hq_eq]
    field_simp [sub_ne_zero.mpr hp.ne']
    ring
  have hsmooth :
      is_l_smooth_on (halfSquaredLpNorm n q) Set.univ (Real.toNNReal (1 / (p - 1))) := by
    have hnonneg : 0 ≤ 1 / (p - 1) := by positivity
    simpa [hq_sub, Real.toNNReal_of_nonneg hnonneg] using
      (HalfSquaredLpNorm.isLSmooth (n := n) (p := q) hq_ge_two)
  let G : Type := WithLp (ENNReal.ofReal q) (Fin n → ℝ)
  let h : StrongDual ℝ G → ℝ := fun η ↦
    (conjugate_function_strongDual (halfSquaredLpNorm n q).toEReal η).toReal
  let A : E →ₗ[ℝ] StrongDual ℝ G := pairingStrongDualMap n p q
  have hA : ∀ x : E, ‖A x‖ = ‖x‖ := by
    intro x
    simpa [A] using pairingStrongDualMap_norm n hpqENN x
  have hstar :
      StrongConvexOn Set.univ (p - 1) h := by
    simpa [h] using
      (qSideConjugateStrongConvexOn (n := n) (p := p) (q := q) hp_sub_pos hsmooth)
  have hpull :
      StrongConvexOn Set.univ (p - 1) (fun x : E ↦ h (A x)) := by
    exact strongConvexOn_comp_of_normPreservingLinearMap A hA hstar
  have heq : (fun x : E ↦ h (A x)) = halfSquaredLpNorm n p := by
    funext x
    have hhalf :
        (halfSquaredLpNorm n q).toEReal =
          (fun z : G ↦ ((((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
      funext z
      simp [halfSquaredLpNorm, Function.toEReal, div_eq_mul_inv, mul_comm]
    have hconj :
        conjugate_function_strongDual (halfSquaredLpNorm n q).toEReal (A x) =
          ((halfSquaredLpNorm n p x : ℝ) : EReal) := by
      rw [hhalf]
      simpa [A, pairingStrongDualMap] using
        (conjugateHalfSquaredLpNorm_applyLpPairingDual (n := n) (p := p) hp hp₂ x)
    have := congrArg EReal.toReal hconj
    simpa [h] using this
  simpa [heq] using hpull

/-- Source-facing strong-convexity predicate for the half-squared `ℓ_p` norm, with the canonical
`WithLp` ambient structure derived internally from `1 < p`. -/
def IsStronglyConvex (n : ℕ) (p : ℝ) (hp : 1 < p) : Prop :=
  letI := factOneLeOfRealOfOneLt hp
  StrongConvexOn Set.univ (p - 1) (halfSquaredLpNorm n p)

/-- Unfolding `HalfSquaredLpNorm.IsStronglyConvex` recovers the canonical owner statement with the
hidden `WithLp` side condition restored from `1 < p`. -/
@[simp] theorem IsStronglyConvex_iff (hp : 1 < p) :
    IsStronglyConvex n p hp ↔
      letI := factOneLeOfRealOfOneLt hp
      StrongConvexOn Set.univ (p - 1) (halfSquaredLpNorm n p) := by
  simp [IsStronglyConvex]

/-- A `HalfSquaredLpNorm.IsStronglyConvex` hypothesis may be applied directly as the canonical
owner statement. -/
theorem IsStronglyConvex.apply {hp : 1 < p} (h : IsStronglyConvex n p hp) :
    letI := factOneLeOfRealOfOneLt hp
    StrongConvexOn Set.univ (p - 1) (halfSquaredLpNorm n p) := by
  simpa using h

/-- The half-squared `ℓ_p` norm induces the Chapter 5 strong-convexity class on its canonical
extended-real-valued coercion when `1 < p ≤ 2`. -/
instance instIsStronglyConvexFunction [Fact (1 < p)] [Fact (p ≤ 2)] :
    is_strongly_convex_function (halfSquaredLpNorm n p).toEReal (p - 1) := by
  -- Transport the owner theorem through `is_strongly_convex_function_iff_strongConvexOn_toReal`.
  refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
  refine ⟨by linarith [‹Fact (1 < p)›.1], ?_, ?_⟩
  · intro x
    simp [Function.toEReal]
  · have hdom : effective_domain (halfSquaredLpNorm n p).toEReal = Set.univ := by
      ext x
      simp [Function.toEReal, effective_domain]
    rw [hdom]
    simpa [Function.toEReal] using HalfSquaredLpNorm.isStronglyConvex (n := n) (p := p)

end HalfSquaredLpNorm

-- Proof sketch: use the standard uniform convexity of finite-dimensional `ℓ_p` spaces for
-- `1 < p ≤ 2`, in the form of Clarkson's inequality or the equivalent Hessian lower bound for
-- `x ↦ ‖x‖² / 2`, to verify the defining Jensen inequality for `StrongConvexOn` on `Set.univ`.
/-- Proposition 5.15: for `1 < p ≤ 2`, the half-squared `ℓ_p` norm on the canonical `WithLp`
model of `ℝ^n` is globally `(p - 1)`-strongly convex. -/
theorem half_squared_lp_norm_is_strongly_convex
    (hp : 1 < p) (hp₂ : p ≤ 2) :
    HalfSquaredLpNorm.IsStronglyConvex n p hp := by
  dsimp [HalfSquaredLpNorm.IsStronglyConvex]
  letI : Fact (1 < p) := ⟨hp⟩
  letI : Fact (p ≤ 2) := ⟨hp₂⟩
  simpa using HalfSquaredLpNorm.isStronglyConvex

-- Proof sketch: translate the owner-level `StrongConvexOn` statement into the defining quadratic
-- Jensen inequality for the finite-valued extended-real-valued function
-- `z ↦ ((‖z‖² / 2 : ℝ) : EReal)`, observing that its effective domain is all of `E` and that it
-- never takes the value `-∞`; this companion is now provided by the canonical instance
-- `HalfSquaredLpNorm.instIsStronglyConvexFunction` rather than a duplicate theorem wrapper.

end
