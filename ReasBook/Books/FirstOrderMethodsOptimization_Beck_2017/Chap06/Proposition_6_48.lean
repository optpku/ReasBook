/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_33
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_47

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (ofLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 6.48 is `source-facing`: the textbook statement computes the proximal operator of
the `ℓ∞` norm on a finite Euclidean product, specialized in the source to `ℝ^n`, through the
Euclidean projection onto the `ℓ¹` unit ball. Domain sampling points to the existing chapter
owners `prox[...]`, `P[...]`, and `B₁[α]`; Proposition 6.48 is therefore a `source-facing`
finite-product specialization of the support-function proximal formula from Theorem 6.46 rather
than a place to introduce a second coordinate-level projection or ball wrapper. On the coordinate
model `y.ofLp : ι → ℝ`, the ambient norm is already the canonical `ℓ∞` norm, so the public
surface should use `‖y.ofLp‖` directly rather than the redundant re-packaging
`‖toLp ⊤ y.ofLp‖`. The primitive data are only the scaled `ℓ∞` objective and the already-owned
closed `ℓ¹` unit ball `B₁[(1 : ℝ)]`.
-/

-- Proof sketch: specialize the support-function proximal formula of Theorem 6.46 to the support
-- function of the closed `ℓ¹` unit ball, using that on `E = EuclideanSpace ℝ ι` the support
-- function of `B₁[(1 : ℝ)]` is the coordinate `ℓ∞` norm `y ↦ ‖y.ofLp‖`. Rewriting the singleton
-- conclusion of Theorem 6.46 through the chapter's set-valued projection notation gives the
-- displayed affine-image identity.
/-- Helper for Proposition 6.48: the auxiliary seminorm whose value at `x` is the coordinate
`ℓ∞` norm `‖x.ofLp‖`. -/
def coordinateLinftySeminorm : Seminorm ℝ E :=
  (normSeminorm ℝ (WithLp (⊤ : ENNReal) (ι → ℝ))).comp
    (((WithLp.linearEquiv (p := (⊤ : ENNReal)) (K := ℝ) (V := ι → ℝ)).symm.toLinearMap).comp
      ((WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := ι → ℝ)).toLinearMap))

-- Proof sketch: unfold the pullback seminorm and identify the transported norm with the `ℓ∞`
-- norm of the coordinate vector via `WithLp.norm_toLp`.
/-- Helper for Proposition 6.48: evaluating `coordinateLinftySeminorm` recovers the coordinate
`ℓ∞` norm. -/
@[simp] lemma coordinateLinftySeminorm_apply (x : E) :
    coordinateLinftySeminorm x = ‖x.ofLp‖ := by
  simp [coordinateLinftySeminorm]

/-- Helper for Proposition 6.48: the real sign always has norm at most `1`. -/
lemma real_sign_norm_le_one (r : ℝ) : ‖Real.sign r‖ ≤ 1 := by
  rcases lt_trichotomy r 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos]

/-- Helper for Proposition 6.48: multiplying a real number by its sign gives its absolute value. -/
lemma real_mul_sign_eq_abs (r : ℝ) : r * Real.sign r = |r| := by
  rcases lt_trichotomy r 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

-- Proof sketch: the sign vector has each coordinate in `{-1, 0, 1}`, so its `ℓ∞` norm is at
-- most `1`.
/-- Helper for Proposition 6.48: the coordinate sign vector has `ℓ∞` norm at most `1`. -/
lemma coordinate_sign_vector_norm_le_one (y : E) :
    ‖(WithLp.toLp (p := (⊤ : ENNReal)) (fun i : ι ↦ Real.sign (y.ofLp i)))‖ ≤ 1 := by
  -- Each coordinate sign has norm at most `1`, so the coordinate supremum does too.
  have hnn :
      ‖(WithLp.toLp (p := (⊤ : ENNReal)) (fun i : ι ↦ Real.sign (y.ofLp i)))‖₊ ≤
        (1 : NNReal) := by
    rw [PiLp.nnnorm_toLp, Pi.nnnorm_def]
    refine Finset.sup_le fun i hi ↦ ?_
    exact_mod_cast real_sign_norm_le_one (y.ofLp i)
  exact_mod_cast hnn

-- Proof sketch: use Example 6.47's dual-ball criterion. If `y` lies in the dual ball of the
-- coordinate `ℓ∞` seminorm, test against the coordinate sign vector to recover `‖y‖₁ ≤ 1`.
-- Conversely, Hölder's `ℓ¹`/`ℓ∞` estimate bounds every pairing by `‖z.ofLp‖`.
/-- Helper for Proposition 6.48: the dual unit ball of the coordinate `ℓ∞` seminorm is exactly the
closed `ℓ¹` unit ball `B₁[(1 : ℝ)]`. -/
theorem coordinateLinftyDualUnitBall_eq_l1ClosedUnitBall :
    alphaDualUnitBall coordinateLinftySeminorm = (B₁[(1 : ℝ)] : Set E) := by
  ext y
  rw [mem_alphaDualUnitBall_iff_le_seminorm, mem_l1ClosedBall_iff]
  constructor
  · intro hy
    let z : E := WithLp.toLp (p := (2 : ENNReal)) (fun i : ι ↦ Real.sign (y.ofLp i))
    have hz_norm' : ‖WithLp.toLp (p := (⊤ : ENNReal)) z.ofLp‖ ≤ 1 := by
      simpa [z] using coordinate_sign_vector_norm_le_one (ι := ι) y
    have hz_norm : ‖z.ofLp‖ ≤ 1 := by
      simpa using hz_norm'
    have hsum : inner ℝ y z = ‖y‖₁ := by
      -- Pairing with the coordinate sign vector adds up the absolute values of the coordinates.
      calc
        inner ℝ y z = ∑ i, y.ofLp i * Real.sign (y.ofLp i) := by
          simpa [z, dotProduct, mul_comm] using
            EuclideanSpace.inner_toLp_toLp (y.ofLp) (fun i : ι ↦ Real.sign (y.ofLp i))
        _ = ∑ i, |y.ofLp i| := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact real_mul_sign_eq_abs (y.ofLp i)
        _ = ‖y‖₁ := by
          symm
          simp [EuclideanSpace.l1Norm_eq_sum_abs]
    have hbound : ‖y‖₁ ≤ ‖z.ofLp‖ := by
      simpa [coordinateLinftySeminorm_apply, hsum] using hy z
    exact hbound.trans hz_norm
  · intro hy z
    have hcoord (i : ι) : |z.ofLp i| ≤ ‖z.ofLp‖ := by
      have hcoord' : ‖z.ofLp i‖₊ ≤ ‖z.ofLp‖₊ := by
        rw [Pi.nnnorm_def]
        exact Finset.le_sup (f := fun b : ι => ‖z.ofLp b‖₊) (Finset.mem_univ i)
      exact_mod_cast hcoord'
    have hinner_eq : inner ℝ y z = ∑ i, y.ofLp i * z.ofLp i := by
      simpa [dotProduct, mul_comm] using EuclideanSpace.inner_toLp_toLp (y.ofLp) (z.ofLp)
    have hinner_le : inner ℝ y z ≤ ∑ i, |y.ofLp i| * |z.ofLp i| := by
      -- First bound the pairing by the sum of absolute coordinate products.
      calc
        inner ℝ y z ≤ |inner ℝ y z| := le_abs_self _
        _ = |∑ i, y.ofLp i * z.ofLp i| := by rw [hinner_eq]
        _ ≤ ∑ i, |y.ofLp i * z.ofLp i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |y.ofLp i| * |z.ofLp i| := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [abs_mul]
    -- Then dominate each coordinate of `z` by its `ℓ∞` norm and sum the resulting `ℓ¹` bound.
    calc
      inner ℝ y z ≤ ∑ i, |y.ofLp i| * |z.ofLp i| := hinner_le
      _ ≤ ∑ i, |y.ofLp i| * ‖z.ofLp‖ := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
      _ = ‖y‖₁ * ‖z.ofLp‖ := by
        rw [← Finset.sum_mul]
        simp [EuclideanSpace.l1Norm_eq_sum_abs]
      _ = ‖z.ofLp‖ * ‖y‖₁ := by rw [mul_comm]
      _ ≤ ‖z.ofLp‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = ‖z.ofLp‖ := by ring
      _ ≤ coordinateLinftySeminorm z := by
        simp [coordinateLinftySeminorm_apply]

-- Proof sketch: Example 6.47 is phrased using `alphaNormPenalty`, and for the coordinate `ℓ∞`
-- seminorm that owner is exactly the target integrand.
/-- Helper for Proposition 6.48: the scaled coordinate `ℓ∞` penalty is `alphaNormPenalty` for
`coordinateLinftySeminorm`. -/
lemma coordinateLinftyPenalty_eq_alphaNormPenalty (lam : ℝ) :
    (fun y : E ↦ ((lam * ‖y.ofLp‖ : ℝ) : EReal)) = alphaNormPenalty coordinateLinftySeminorm lam :=
  by
  funext y
  -- Evaluate the generic penalty and then rewrite the auxiliary seminorm pointwise.
  rw [alphaNormPenalty_apply, coordinateLinftySeminorm_apply]

/-- Proposition 6.48: on a finite Euclidean product `E = EuclideanSpace ℝ ι`, specializing to
`ℝ^n` when `ι = Fin n`, the proximal mapping of the scaled `ℓ∞` norm
`y ↦ λ ‖y.ofLp‖` is the affine image of the projection set onto the closed `ℓ¹` unit ball
`B₁[(1 : ℝ)]`. This is the chapter's set-valued rendering of the textbook identity
`prox_{λ ‖·‖∞}(x) = x - λ P_{B_{‖·‖₁}[0,1]}(x / λ)`. -/
theorem prox_linftyNorm_eq_sub_smul_projection_mapping_l1ClosedUnitBall
    (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[fun y : E ↦ ((lam * ‖y.ofLp‖ : ℝ) : EReal)] x =
      Set.image (fun u : E ↦ x - lam • u)
        (P[B₁[(1 : ℝ)]] (lam⁻¹ • x)) := by
  -- Rewrite the target penalty through Example 6.47's generic seminorm owner.
  rw [coordinateLinftyPenalty_eq_alphaNormPenalty]
  -- Apply the generic prox formula for a norm and identify its dual unit ball with `B₁[1]`.
  rw [prox_alphaNormPenalty_eq_sub_smul_projection_mapping_alphaDualUnitBall
    (alpha := coordinateLinftySeminorm) lam hlam x]
  rw [coordinateLinftyDualUnitBall_eq_l1ClosedUnitBall]

end
