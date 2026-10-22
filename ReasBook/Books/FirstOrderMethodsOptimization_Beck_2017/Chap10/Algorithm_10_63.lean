/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_61

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (ofLp toLp)
open scoped Gradient

section

variable {ι : Type*} [Fintype ι]

local notation "E" => WithLp 1 (ι → ℝ)
local notation "E₂" => EuclideanSpace ℝ ι
local notation "coordToL1" => (fun z : E₂ ↦ toLp (1 : ENNReal) (ofLp z))
local notation "coordToL2" => (fun x : E ↦ toLp 2 (ofLp x))
local notation "e[" i "]" => (EuclideanSpace.basisFun ι ℝ i : E₂)

/- Algorithm 10.63 is a `bridge/view` item in the chapter's non-Euclidean first-order API.

Domain sampling identifies the three relevant layers already present in the project:
- `source-facing`: the textbook coordinate rule that picks an index
  `i_k ∈ arg max_i |∂ f(x^k) / ∂ x_i|` and moves along the signed basis vector in that coordinate;
- `core/canonical`: the Chapter 10 owner recursion
  `non_euclidean_gradient_method` and admissibility predicate
  `non_euclidean_gradient_method_is_admissible` from Algorithm 10.61 on the primal
  `WithLp 1` model, together with the owner set `Λ[·]`;
- `bridge/view`: the signed active-coordinate vector produced by the selected maximizing index,
  viewed as an `ℓ₁` primal counterpart after transport from the Euclidean coordinate model via
  `coordToL1`, with Proposition 10.60 identifying its `Λ[·]` membership.

The primitive source data here are therefore only the index-selection rule and the resulting
signed basis vector. The generated trajectory is already owned by Algorithm 10.61, so this file
keeps only the coordinate realization of the chosen counterpart and the corresponding textbook
update formulas. For the basis vector itself, the canonical owner is `EuclideanSpace.basisFun`,
while `EuclideanSpace.single i 1` is only its coordinate-level view from Chapter 1. -/

/-- The signed coordinate vector `sgn ((∇ f x)_i) e_i` determined by the selected index `i`. This
is the source-facing coordinate realization of the `ℓ₁` primal counterpart used by Algorithm
10.63. -/
def l1_non_euclidean_gradient_counterpart
    (f : E₂ → ℝ) (x : E₂) (i : ι) : E₂ :=
  Real.sign ((∇ f x) i) • e[i]

/-- Expanding `l1_non_euclidean_gradient_counterpart` gives the signed basis vector
`sgn ((∇ f x)_i) e_i`. -/
@[simp] theorem l1_non_euclidean_gradient_counterpart_eq
    (f : E₂ → ℝ) (x : E₂) (i : ι) :
    l1_non_euclidean_gradient_counterpart f x i =
      Real.sign ((∇ f x) i) • e[i] :=
  rfl

/-- The counterpart-selection rule induced by an index-selection rule `iSel`: at time `k` and
owner point `x`, use the signed basis vector in the selected coordinate of its Euclidean view
`coordToL2 x`, then transport it back to the primal `ℓ₁` model. -/
def l1_non_euclidean_gradient_counterpart_rule
    (f : E₂ → ℝ) (iSel : ℕ → E₂ → ι) : ℕ → E → E :=
  fun k x ↦
    coordToL1 (l1_non_euclidean_gradient_counterpart f (coordToL2 x) (iSel k (coordToL2 x)))

/-- Evaluating the induced counterpart-selection rule applies
`l1_non_euclidean_gradient_counterpart` to the selected Euclidean coordinate and transports the
result to the primal `ℓ₁` owner space. -/
@[simp] theorem l1_non_euclidean_gradient_counterpart_rule_apply
    (f : E₂ → ℝ) (iSel : ℕ → E₂ → ι) (k : ℕ) (x : E) :
    l1_non_euclidean_gradient_counterpart_rule f iSel k x =
      coordToL1
        (l1_non_euclidean_gradient_counterpart f (coordToL2 x) (iSel k (coordToL2 x))) :=
  rfl

/-- Helper for Algorithm 10.63: the `ℓ₁`-to-Euclidean coordinate transport is the continuous
linear equivalence induced by the two `WithLp.linearEquiv` coordinate identifications. -/
abbrev coordToL2ContinuousLinearEquiv : E ≃L[ℝ] E₂ :=
  ((WithLp.linearEquiv (1 : ENNReal) ℝ (ι → ℝ)).trans
      (WithLp.linearEquiv (2 : ENNReal) ℝ (ι → ℝ)).symm).toContinuousLinearEquiv

/-- Helper for Algorithm 10.63: `coordToL2ContinuousLinearEquiv` acts by the coordinate transport
`coordToL2`. -/
@[simp] theorem coordToL2ContinuousLinearEquiv_apply (x : E) :
    coordToL2ContinuousLinearEquiv x = coordToL2 x :=
  rfl

/-- Helper for Algorithm 10.63: the inverse Euclidean-to-`ℓ₁` transport acts by `coordToL1`. -/
@[simp] theorem coordToL2ContinuousLinearEquiv_symm_apply (x : E₂) :
    coordToL2ContinuousLinearEquiv.symm x = coordToL1 x :=
  rfl

/-- Helper for Algorithm 10.63: the `(1, ∞)` pairing functional has operator norm equal to the
`ℓ∞` norm of its coefficient vector. -/
private lemma lpPairingDual_one_operatorNorm_eq_linf (a : WithLp (⊤ : ENNReal) (ι → ℝ)) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))‖ = ‖ofLp a‖ := by
  classical
  let T := LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))
  have hupper : ‖T‖ ≤ ‖ofLp a‖ := by
    refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _) ?_
    intro x
    calc
      ‖T x‖ = ‖dotProduct (ofLp x) (ofLp a)‖ := by
        simp [T, lpPairingDual_apply]
      _ ≤ ∑ i, ‖ofLp x i * ofLp a i‖ := by
        simpa [dotProduct] using norm_sum_le Finset.univ (fun i : ι ↦ ofLp x i * ofLp a i)
      _ = ∑ i, ‖ofLp x i‖ * ‖ofLp a i‖ := by
        simp [norm_mul]
      _ ≤ ∑ i, ‖ofLp x i‖ * ‖ofLp a‖ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        gcongr
        rw [Pi.norm_def]
        simpa using
          (@Finset.le_sup NNReal ι inferInstance inferInstance Finset.univ
            (fun j : ι ↦ ‖ofLp a j‖₊) i (Finset.mem_univ i))
      _ = ∑ i, ‖ofLp a‖ * ‖ofLp x i‖ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [mul_comm]
      _ = ‖ofLp a‖ * ∑ i, ‖ofLp x i‖ := by
        rw [Finset.mul_sum]
      _ = ‖ofLp a‖ * ‖x‖ := by
        rw [PiLp.norm_eq_sum (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp
  by_cases hι : Nonempty ι
  · letI := hι
    obtain ⟨i, hmax⟩ := Finite.exists_max (fun j : ι ↦ |(ofLp a) j|)
    have hunit :
        ‖toLp (1 : ENNReal) ((Pi.single i (Real.sign ((ofLp a) i)) : ι → ℝ))‖ ≤ 1 := by
      calc
        ‖toLp (1 : ENNReal) ((Pi.single i (Real.sign ((ofLp a) i)) : ι → ℝ))‖ =
            ‖Real.sign ((ofLp a) i)‖ := by
          simp
      _ ≤ 1 := by
          rcases lt_trichotomy ((ofLp a) i) 0 with hneg | hzero | hpos
          · simp [Real.sign_of_neg hneg]
          · simp [hzero]
          · simp [Real.sign_of_pos hpos]
    have hvalue :
        ‖T (toLp (1 : ENNReal) ((Pi.single i (Real.sign ((ofLp a) i)) : ι → ℝ)))‖ =
          |(ofLp a) i| := by
      have hsignmul :
          |Real.sign ((ofLp a) i) * (ofLp a) i| = |(ofLp a) i| := by
        rcases lt_trichotomy ((ofLp a) i) 0 with hneg | hzero | hpos
        · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
        · simp [hzero]
        · simp [Real.sign_of_pos hpos, abs_of_pos hpos]
      simpa [T, lpPairingDual_apply, single_dotProduct, Real.norm_eq_abs] using hsignmul
    have hcoord : ‖ofLp a‖ = |(ofLp a) i| := by
      rw [Pi.norm_def]
      have hsup : Finset.univ.sup (fun j : ι ↦ ‖ofLp a j‖₊) = ‖ofLp a i‖₊ := by
        refine le_antisymm ?_
          (@Finset.le_sup NNReal ι inferInstance inferInstance Finset.univ
            (fun j : ι ↦ ‖ofLp a j‖₊) i (Finset.mem_univ i))
        refine Finset.sup_le ?_
        intro j hj
        exact_mod_cast hmax j
      rw [hsup]
      simp [Real.norm_eq_abs]
    have hlower : ‖ofLp a‖ ≤ ‖T‖ := by
      calc
        ‖ofLp a‖ = ‖T (toLp (1 : ENNReal) ((Pi.single i (Real.sign ((ofLp a) i)) : ι → ℝ)))‖ := by
          rw [hcoord, hvalue]
        _ ≤ ‖T‖ := by
          simpa [T] using
            T.unit_le_opNorm
              (toLp (1 : ENNReal) ((Pi.single i (Real.sign ((ofLp a) i)) : ι → ℝ))) hunit
    exact le_antisymm hupper hlower
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have ha : a = 0 := Subsingleton.elim _ _
    simp [ha]

/-- Helper for Algorithm 10.63: in `ℝ≥0`, a maximizing coordinate realizes the finite supremum
of the coordinate norms. -/
lemma finite_sup_nnnorm_eq_of_maximizer
    (a : ι → ℝ) (i : ι) (hmax : ∀ j : ι, |a j| ≤ |a i|) :
    Finset.univ.sup (fun j : ι ↦ ‖a j‖₊) = ‖a i‖₊ := by
  -- Compare the finite supremum directly with the maximizing coordinate inside `ℝ≥0`.
  refine le_antisymm ?_
    (@Finset.le_sup NNReal ι inferInstance inferInstance Finset.univ
      (fun j : ι ↦ ‖a j‖₊) i (Finset.mem_univ i))
  refine Finset.sup_le ?_
  intro j hj
  exact_mod_cast hmax j

/-- Helper for Algorithm 10.63: a maximizing coordinate realizes the `ℓ∞` norm of the
coefficient vector. -/
lemma linf_norm_eq_abs_of_coordinate_maximizer
    (a : ι → ℝ) (i : ι) (hmax : ∀ j : ι, |a j| ≤ |a i|) :
    ‖toLp (⊤ : ENNReal) a‖ = |a i| := by
  -- Rewrite the `ℓ∞` norm as the finite supremum of coordinate norms and substitute the
  -- maximizing-coordinate value.
  rw [PiLp.norm_toLp, Pi.norm_def, finite_sup_nnnorm_eq_of_maximizer a i hmax]
  simp [Real.norm_eq_abs]

/-- Helper for Algorithm 10.63: the Euclidean Riesz pairing on the coordinate model is the
coordinate dot product. -/
private lemma toDualMap_apply_eq_dotProduct (u v : E₂) :
    ((InnerProductSpace.toDualMap ℝ E₂ v) u : ℝ) = dotProduct (ofLp u) (ofLp v) := by
  -- Convert the Euclidean inner product to the explicit coordinate formula.
  simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp (ofLp v) (ofLp u))

/-- Helper for Algorithm 10.63: after transporting an `ℓ₁` vector to Euclidean coordinates, the
Euclidean Riesz functional evaluates exactly as the canonical `(1, ∞)` pairing functional. -/
lemma toDualMap_apply_coordToL2_eq_lpPairingDual_apply
    (u : E) (v : E₂) :
    ((InnerProductSpace.toDualMap ℝ E₂ v) (coordToL2 u) : ℝ) =
      LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp v)) u := by
  -- Rewrite the Euclidean pairing into the coordinate dot product, then recognize the owner
  -- `(1, ∞)` pairing formula.
  calc
    ((InnerProductSpace.toDualMap ℝ E₂ v) (coordToL2 u) : ℝ) =
        dotProduct (ofLp u) (ofLp v) := by
      simpa using (toDualMap_apply_eq_dotProduct (coordToL2 u) v)
    _ = LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp v)) u := by
      simp [lpPairingDual_apply]

-- Route correction: the owner derivative on `WithLp 1` should be rewritten once through the
-- coordinate transport, then all later trajectory proofs can stay on Algorithm 10.61's surface.
/-- Helper for Algorithm 10.63: pulling back `f` along `coordToL2` identifies the Fréchet
derivative on the `ℓ₁` owner space with the canonical `lpPairingDual` functional of the Euclidean
gradient. -/
lemma fderiv_pullback_coordToL2_eq_lpPairingDual_gradient
    (f : E₂ → ℝ) (x : E) (hf : DifferentiableAt ℝ f (coordToL2 x)) :
    fderiv ℝ (fun y : E ↦ f (coordToL2 y)) x =
      LinearMap.toContinuousLinearMap
        (lpPairingDual (1 : ENNReal) (ofLp (∇ f (coordToL2 x)))) := by
  -- Apply the chain rule through the coordinate equivalence, then rewrite the composed Euclidean
  -- Riesz functional as the canonical `(1, ∞)` pairing functional.
  calc
    fderiv ℝ (fun y : E ↦ f (coordToL2 y)) x =
        (fderiv ℝ f (coordToL2 x)).comp coordToL2ContinuousLinearEquiv.toContinuousLinearMap := by
      exact
        (hf.hasFDerivAt.comp x
          coordToL2ContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
    _ =
        ((InnerProductSpace.toDual ℝ E₂) (∇ f (coordToL2 x))).comp
          coordToL2ContinuousLinearEquiv.toContinuousLinearMap := by
      ext u
      simpa [ContinuousLinearMap.comp_apply, coordToL2ContinuousLinearEquiv_apply,
        InnerProductSpace.toDual_apply_apply] using
        (show
            fderiv ℝ f (coordToL2 x) (coordToL2 u) = inner ℝ (∇ f (coordToL2 x)) (coordToL2 u) from
          HasGradientAt.fderiv_apply hf.hasGradientAt)
    _ =
        LinearMap.toContinuousLinearMap
          (lpPairingDual (1 : ENNReal) (ofLp (∇ f (coordToL2 x)))) := by
      rw [InnerProductSpace.toDual_apply_eq_toDualMap_apply]
      ext u
      -- Evaluate both composed maps on the same primal vector and use the exact adapter.
      simpa [ContinuousLinearMap.comp_apply] using
        (toDualMap_apply_coordToL2_eq_lpPairingDual_apply u (∇ f (coordToL2 x)))

/-- Helper for Algorithm 10.63: multiplying a real number by its sign gives its absolute value. -/
private lemma real_sign_mul_eq_abs (t : ℝ) : Real.sign t * t = |t| := by
  -- Split on the sign of the scalar and reduce to the defining formulas for `Real.sign`.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- Helper for Algorithm 10.63: the real sign has norm at most `1`. -/
private lemma real_sign_norm_le_one (t : ℝ) : ‖Real.sign t‖ ≤ 1 := by
  -- The sign can only take the values `-1`, `0`, and `1`.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos]

-- Proof sketch: Proposition 10.60 identifies `Λ[lpPairingDual 1 a]` with the signed
-- active-coordinate face of the `ℓ∞` vector `a`. A basis vector supported on a maximizing
-- coordinate is an extreme point of that face, so its `ℓ₁` transport belongs to the owner set.
-- Because mathlib's gradient is totalized, no differentiability hypothesis is needed here: in the
-- nondifferentiable case `∇ f x = 0`, the selected signed basis vector is `0`, and `0 ∈ Λ[0]`.
/-- If `i` attains the maximum absolute coordinate of the totalized gradient `∇ f x`, then the
selected signed basis vector, transported to the chapter's canonical `ℓ₁` model, is a primal
counterpart of the corresponding `ℓ∞` gradient coefficient vector. -/
theorem l1_non_euclidean_gradient_counterpart_mem_primalCounterparts
    {f : E₂ → ℝ} {x : E₂} {i : ι}
    (hmax : ∀ j : ι, |(∇ f x) j| ≤ |(∇ f x) i|) :
    coordToL1 (l1_non_euclidean_gradient_counterpart f x i) ∈
      Λ[LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp (∇ f x)))] := by
  classical
  -- Unfold `Λ[·]`: the transported signed basis vector must lie in the `ℓ₁` unit ball and attain
  -- the operator norm of the `(1, ∞)` pairing functional.
  have hsingle :
      coordToL1 (l1_non_euclidean_gradient_counterpart f x i) =
        toLp (1 : ENNReal) (Pi.single i (Real.sign ((∇ f x) i))) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [l1_non_euclidean_gradient_counterpart, EuclideanSpace.basisFun_apply]
    · simp [l1_non_euclidean_gradient_counterpart, Pi.single, hji,
        EuclideanSpace.basisFun_apply]
  constructor
  · -- Transport the Euclidean signed basis vector to the corresponding single-coordinate `ℓ₁`
    -- vector and read off its norm.
    calc
      ‖coordToL1 (l1_non_euclidean_gradient_counterpart f x i)‖ =
          ‖Real.sign ((∇ f x) i)‖ := by
        rw [hsingle]
        simp
      _ ≤ 1 := by
        simpa using real_sign_norm_le_one ((∇ f x) i)
  · -- Evaluate the pairing on that single-coordinate vector and compare it with the `ℓ∞` norm
    -- attained at the maximizing coordinate.
    calc
      LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp (∇ f x)))
          (coordToL1 (l1_non_euclidean_gradient_counterpart f x i)) =
          Real.sign ((∇ f x) i) * (∇ f x) i := by
        rw [hsingle]
        simp [lpPairingDual_apply, single_dotProduct]
      _ = |(∇ f x) i| := real_sign_mul_eq_abs ((∇ f x) i)
      _ = ‖ofLp (∇ f x)‖ := by
        symm
        simpa [PiLp.norm_toLp] using
          (linf_norm_eq_abs_of_coordinate_maximizer (ofLp (∇ f x)) i hmax)
      _ = ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp (∇ f x)))‖ := by
        symm
        simpa using
          (lpPairingDual_one_operatorNorm_eq_linf
            (toLp (⊤ : ENNReal) (ofLp (∇ f x))))

/-- One `ℓ₁` non-Euclidean gradient step at `x` with curvature `L` and selected coordinate `i`,
namely
`x - (‖∇ f(x)‖_∞ / L) sgn ((∇ f(x))_i) e_i`. -/
def l1_non_euclidean_gradient_step
    (f : E₂ → ℝ) (L : PosReal) (i : ι) (x : E₂) : E₂ :=
  x - (‖(∇ f x).ofLp‖ / (L : ℝ)) • l1_non_euclidean_gradient_counterpart f x i

/-- Expanding `l1_non_euclidean_gradient_step` recovers the update
`x - (‖∇ f(x)‖_∞ / L) sgn ((∇ f(x))_i) e_i`. -/
@[simp] theorem l1_non_euclidean_gradient_step_eq
    (f : E₂ → ℝ) (L : PosReal) (i : ι) (x : E₂) :
    l1_non_euclidean_gradient_step f L i x =
      x - (‖(∇ f x).ofLp‖ / (L : ℝ)) •
        (Real.sign ((∇ f x) i) • e[i]) := by
  simp [l1_non_euclidean_gradient_step]

section Trajectory

-- Spell out the Euclidean coordinate type in these section variables.  With a local notation
-- here, Lean may elaborate each occurrence with a fresh, unresolved index type before `ι` is
-- registered as a dependency of the section variable; the unresolved metavariable then
-- contaminates every trajectory theorem below.
variable (f : EuclideanSpace ℝ ι → ℝ)
  (iSel : ℕ → EuclideanSpace ℝ ι → ι)
  (L : ℕ → PosReal) (x0 : EuclideanSpace ℝ ι)

local notation "f₁" => fun x : E ↦ f (coordToL2 x)
local notation "counterpart" => l1_non_euclidean_gradient_counterpart_rule f iSel
local notation "x[" k "]" => non_euclidean_gradient_method f₁ counterpart L (coordToL1 x0) k
local notation "x₂[" k "]" => coordToL2 (x[k])

/-- Helper for Algorithm 10.63: transporting a Euclidean update through `coordToL1` commutes with
subtracting a scaled direction. -/
lemma coordToL1_coordToL2_sub_smul
    (x : E) (a : ℝ) (v : E₂) :
    coordToL1 (coordToL2 x - a • v) = x - a • coordToL1 v := by
  -- Rewrite the transport as the inverse continuous linear equivalence and use linearity once.
  change coordToL2ContinuousLinearEquiv.symm
      (coordToL2ContinuousLinearEquiv x - a • v) =
    x - a • coordToL2ContinuousLinearEquiv.symm v
  rw [map_sub, map_smul]
  simp

/-- Helper for Algorithm 10.63: at an arbitrary owner point, a maximizing coordinate selects a
primal counterpart of the pulled-back derivative. -/
lemma coordinate_counterpart_rule_mem_primalCounterparts_at_point
    (k : ℕ) (x : E)
    (hf : DifferentiableAt ℝ f (coordToL2 x))
    (hmax : ∀ j : ι, |(∇ f (coordToL2 x)) j| ≤ |(∇ f (coordToL2 x)) (iSel k (coordToL2 x))|) :
    counterpart k x ∈ Λ[fderiv ℝ f₁ x] :=
  -- Rewrite the owner derivative through the Euclidean gradient bridge, then reuse the
  -- maximizing-coordinate counterpart theorem at the Euclidean point `coordToL2 x`.
  (fderiv_pullback_coordToL2_eq_lpPairingDual_gradient f x hf) ▸
    l1_non_euclidean_gradient_counterpart_mem_primalCounterparts hmax

/-- Helper for Algorithm 10.63: at a differentiability point, one owner step is exactly the
transported textbook coordinate step. -/
lemma owner_step_eq_coordinate_step_of_differentiable
    (k : ℕ) (Lk : PosReal) (x : E)
    (hf : DifferentiableAt ℝ f (coordToL2 x)) :
    x - (‖fderiv ℝ f₁ x‖ / (Lk : ℝ)) • counterpart k x =
      coordToL1 (l1_non_euclidean_gradient_step f Lk (iSel k (coordToL2 x)) (coordToL2 x)) :=
  -- Rewrite the owner derivative norm to the Euclidean `ℓ∞` gradient norm once, then use the
  -- transport identity for a single scaled Euclidean update.
  let hnorm :
      ‖fderiv ℝ f₁ x‖ = ‖(∇ f (coordToL2 x)).ofLp‖ :=
    Eq.trans
      (congrArg norm
        (fderiv_pullback_coordToL2_eq_lpPairingDual_gradient f x hf))
      (lpPairingDual_one_operatorNorm_eq_linf
        (toLp (⊤ : ENNReal) (ofLp (∇ f (coordToL2 x)))))
  hnorm ▸
    (coordToL1_coordToL2_sub_smul x
      (‖(∇ f (coordToL2 x)).ofLp‖ / (Lk : ℝ))
      (l1_non_euclidean_gradient_counterpart f (coordToL2 x) (iSel k (coordToL2 x)))).symm

/-- Helper for Algorithm 10.63: in the nondifferentiable branch, both the pulled-back derivative
and the Euclidean gradient vanish, so the owner step reduces to the identity update. -/
lemma owner_step_eq_coordinate_step_of_not_differentiable
    (k : ℕ) (Lk : PosReal) (x : E)
    (hnd : ¬ DifferentiableAt ℝ f (coordToL2 x)) :
    x - (‖fderiv ℝ f₁ x‖ / (Lk : ℝ)) • counterpart k x =
      coordToL1 (l1_non_euclidean_gradient_step f Lk (iSel k (coordToL2 x)) (coordToL2 x)) :=
  -- Transport nondifferentiability to the pulled-back objective on the owner space, then rewrite
  -- both step sizes to zero and use the coordinate transport identity.
  let hnd₁ : ¬ DifferentiableAt ℝ f₁ x :=
    fun hf₁ ↦ by
      have hfcomp :
          DifferentiableAt ℝ
            (f ∘ (coordToL2ContinuousLinearEquiv (ι := ι))) x := by
        simpa only [Function.comp_apply, coordToL2ContinuousLinearEquiv_apply] using hf₁
      have hfout :=
        ((coordToL2ContinuousLinearEquiv (ι := ι)).comp_right_differentiableAt_iff
          (f := f) (x := x)).1 hfcomp
      exact hnd (by simpa only [coordToL2ContinuousLinearEquiv_apply] using hfout)
  let hleft : ‖fderiv ℝ f₁ x‖ / (Lk : ℝ) = 0 :=
    Eq.trans
      (congrArg (fun T : E →L[ℝ] ℝ ↦ ‖T‖ / (Lk : ℝ))
        (fderiv_zero_of_not_differentiableAt hnd₁))
      (Eq.trans
        (congrArg (fun t : ℝ ↦ t / (Lk : ℝ)) (norm_zero : ‖(0 : E →L[ℝ] ℝ)‖ = 0))
        (zero_div (Lk : ℝ)))
  let hright : ‖(∇ f (coordToL2 x)).ofLp‖ / (Lk : ℝ) = 0 :=
    Eq.trans
      (congrArg (fun v : E₂ ↦ ‖v.ofLp‖ / (Lk : ℝ))
        (gradient_eq_zero_of_not_differentiableAt hnd))
      (Eq.trans
        (congrArg (fun t : ℝ ↦ t / (Lk : ℝ)) (norm_zero : ‖(0 : ι → ℝ)‖ = 0))
        (zero_div (Lk : ℝ)))
  hleft ▸
    hright ▸
      (coordToL1_coordToL2_sub_smul x 0
        (l1_non_euclidean_gradient_counterpart f (coordToL2 x) (iSel k (coordToL2 x)))).symm

/-- Helper for Algorithm 10.63: at an explicit initialization point, one owner recursion step is
the transported textbook coordinate update. -/
lemma owner_trajectory_succ_eq_coordinate_step
    {xInit : E₂} (k : ℕ) :
    non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) (k + 1) =
      coordToL1
        (l1_non_euclidean_gradient_step f (L k)
          (iSel k
            (coordToL2
              (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k)))
            (coordToL2
              (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k))) := by
  rw [non_euclidean_gradient_method_succ]
  by_cases hf :
      DifferentiableAt ℝ f
        (coordToL2 (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k))
  · exact
      owner_step_eq_coordinate_step_of_differentiable f iSel k (L k)
        (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k) hf
  · exact
      owner_step_eq_coordinate_step_of_not_differentiable f iSel k (L k)
        (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k) hf

/-- Helper for Algorithm 10.63: the coordinate-maximizer hypothesis yields owner admissibility at
an explicit initialization point. -/
lemma coordinate_maximizers_imply_owner_admissibility
    {xInit : E₂}
    (h :
      ∀ k : ℕ,
        DifferentiableAt ℝ f
          (coordToL2 (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k)) ∧
          ∀ j : ι,
            |(∇ f
                (coordToL2 (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k)))
                j| ≤
              |(∇ f
                  (coordToL2
                    (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k)))
                  (iSel k
                    (coordToL2
                      (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k)))|) :
    non_euclidean_gradient_method_is_admissible
      f₁ counterpart L (coordToL1 xInit) :=
  fun k ↦
    ⟨
      (by
        have hfcomp :=
          ((coordToL2ContinuousLinearEquiv (ι := ι)).comp_right_differentiableAt_iff
            (f := f)
            (x := non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k)).2
              (by
                simpa only [coordToL2ContinuousLinearEquiv_apply] using (h k).1)
        simpa only [Function.comp_apply, coordToL2ContinuousLinearEquiv_apply] using hfcomp),
      coordinate_counterpart_rule_mem_primalCounterparts_at_point f iSel k
        (non_euclidean_gradient_method f₁ counterpart L (coordToL1 xInit) k) (h k).1 (h k).2
    ⟩

/-- One owner-step of Algorithm 10.63 is Algorithm 10.61 specialized to the transported
signed active-coordinate counterpart rule. -/
theorem non_euclidean_gradient_method_succ_l1_counterpart_rule
    (k : ℕ) :
    x[k + 1] =
      coordToL1 (l1_non_euclidean_gradient_step f (L k) (iSel k x₂[k]) x₂[k]) :=
  owner_trajectory_succ_eq_coordinate_step f iSel L k

/-- Algorithm 10.63: in Euclidean coordinates, the canonical owner trajectory satisfies the
textbook update
`x^(k+1) = x^k - (‖∇ f(x^k)‖_∞ / L_k) sgn ((∇ f(x^k))_(i_k)) e_(i_k)`, transported back to the
primal `ℓ₁` model by `coordToL1`. -/
theorem non_euclidean_gradient_method_update_l1_counterpart_rule
    (k : ℕ) :
    x[k + 1] =
      coordToL1
        (x₂[k] - (‖(∇ f x₂[k]).ofLp‖ / (L k : ℝ)) •
          (Real.sign ((∇ f x₂[k]) (iSel k x₂[k])) •
            e[iSel k x₂[k]])) :=
  -- Expand the transported Euclidean step from the predecessor theorem into the textbook update.
  Eq.trans
    (non_euclidean_gradient_method_succ_l1_counterpart_rule f iSel L x0 k)
    (congrArg coordToL1
      (l1_non_euclidean_gradient_step_eq f (L k) (iSel k x₂[k]) x₂[k]))

/-- The textbook coordinate-maximizer condition is a source-facing sufficient condition for the
owner admissibility predicate from Algorithm 10.61. -/
theorem non_euclidean_gradient_method_is_admissible_of_coordinate_maximizers
    (h :
      ∀ k : ℕ,
        DifferentiableAt ℝ f x₂[k] ∧
          ∀ j : ι, |(∇ f x₂[k]) j| ≤ |(∇ f x₂[k]) (iSel k x₂[k])|) :
    non_euclidean_gradient_method_is_admissible
      f₁ counterpart L (coordToL1 x0) :=
  coordinate_maximizers_imply_owner_admissibility f iSel L h

/-- Along the canonical owner trajectory, the selected signed coordinate vector is a primal
counterpart of the current `ℓ∞` gradient coefficient vector whenever the selected coordinate
maximizes the absolute gradient coordinate. -/
theorem coordinate_counterpart_mem_primalCounterparts_along_non_euclidean_gradient_method
    (h :
      ∀ k : ℕ, ∀ j : ι, |(∇ f x₂[k]) j| ≤ |(∇ f x₂[k]) (iSel k x₂[k])|)
    (k : ℕ) :
    coordToL1 (l1_non_euclidean_gradient_counterpart f x₂[k] (iSel k x₂[k])) ∈
      Λ[LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp (∇ f x₂[k])))] :=
  l1_non_euclidean_gradient_counterpart_mem_primalCounterparts (h k)

end Trajectory

end
