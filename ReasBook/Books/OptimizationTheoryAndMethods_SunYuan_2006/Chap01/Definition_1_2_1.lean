/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped BigOperators

-- Analogues checked for this item: `Seminorm`, `NormedSpace.Core`,
-- `PiLp.norm_seminormedAddCommGroupToPi`, `PiLp.norm_eq_of_nat`, `lp.norm_eq_ciSup`,
-- `Finset.sup'`, `Matrix.PosDef`.

variable {n : ℕ}

/-- Source notion for Chapter01 Definition 1.2.1: a map `f : (Fin n → ℝ) → ℝ` is a vector norm on
`ℝ^n` when it is
nonnegative, vanishes exactly at `0`, is absolutely homogeneous, and satisfies the triangle
inequality. -/
class IsVectorNorm (f : (Fin n → ℝ) → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  eq_zero_iff : ∀ x, f x = 0 ↔ x = 0
  smul_eq : ∀ (a : ℝ) (x : Fin n → ℝ), f (a • x) = |a| * f x
  add_le : ∀ x y : Fin n → ℝ, f (x + y) ≤ f x + f y

/-- Unfolding formula for `IsVectorNorm`. -/
theorem isVectorNorm_iff (f : (Fin n → ℝ) → ℝ) :
    IsVectorNorm f ↔
      (∀ x, 0 ≤ f x) ∧
        (∀ x, f x = 0 ↔ x = 0) ∧
        (∀ (a : ℝ) (x : Fin n → ℝ), f (a • x) = |a| * f x) ∧
        ∀ x y : Fin n → ℝ, f (x + y) ≤ f x + f y := by
  constructor
  · intro hf
    exact ⟨hf.nonneg, hf.eq_zero_iff, hf.smul_eq, hf.add_le⟩
  · rintro ⟨hnonneg, hzero, hsmul, hadd⟩
    exact ⟨hnonneg, hzero, hsmul, hadd⟩

namespace IsVectorNorm

variable {f : (Fin n → ℝ) → ℝ}

/-- Any vector norm vanishes at the zero vector. -/
theorem map_zero (hf : IsVectorNorm f) : f 0 = 0 :=
  (hf.eq_zero_iff 0).2 rfl

/-- Any vector norm is invariant under negation. -/
theorem map_neg (hf : IsVectorNorm f) (x : Fin n → ℝ) : f (-x) = f x := by
  simpa using hf.smul_eq (-1) x

/-- A vector norm on `ℝ^n` defines a real seminorm. -/
noncomputable def toSeminorm (hf : IsVectorNorm f) : Seminorm ℝ (Fin n → ℝ) :=
  Seminorm.of f hf.add_le fun a x ↦ by
    simpa using hf.smul_eq a x

@[simp] theorem toSeminorm_apply (hf : IsVectorNorm f) (x : Fin n → ℝ) :
    hf.toSeminorm x = f x :=
  rfl

/-- The induced seminorm vanishes exactly at the zero vector. -/
theorem toSeminorm_eq_zero_iff (hf : IsVectorNorm f) (x : Fin n → ℝ) :
    hf.toSeminorm x = 0 ↔ x = 0 :=
  hf.eq_zero_iff x

/-- A vector norm on `ℝ^n` defines an additive group norm. -/
noncomputable def toAddGroupNorm (hf : IsVectorNorm f) : AddGroupNorm (Fin n → ℝ) where
  toFun := f
  map_zero' := hf.map_zero
  add_le' := hf.add_le
  neg' := hf.map_neg
  eq_zero_of_map_eq_zero' x hx := (hf.eq_zero_iff x).1 hx

@[simp] theorem toAddGroupNorm_apply (hf : IsVectorNorm f) (x : Fin n → ℝ) :
    hf.toAddGroupNorm x = f x :=
  rfl

end IsVectorNorm

/-- The `ℓ^p` norm on `ℝ^n` for `1 ≤ p`, implemented via the canonical `PiLp` norm on
functions `Fin n → ℝ`. -/
noncomputable def lpNorm (p : ENNReal) [Fact (1 ≤ p)] : (Fin n → ℝ) → ℝ :=
  fun x ↦ ‖WithLp.toLp p x‖

/-- For `0 < p.toReal`, the `ℓ^p` norm is given by the usual finite-sum formula. -/
theorem lpNorm_eq_sum (p : ENNReal) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : Fin n → ℝ) :
    lpNorm p x = (∑ i : Fin n, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
  -- Transport the canonical `PiLp` formula back to functions on `Fin n`.
  simpa [lpNorm, Real.norm_eq_abs] using PiLp.norm_eq_sum hp (WithLp.toLp p x)

/-- Chapter01 Definition 1.2.1: for `1 ≤ p`, the `ℓ^p` norm is a vector norm on `ℝ^n`. -/
instance lpNorm_isVectorNorm (p : ENNReal) [Fact (1 ≤ p)] :
    IsVectorNorm (fun x : Fin n → ℝ ↦ lpNorm p x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    -- Nonnegativity is inherited from the ambient `PiLp` norm.
    simp [lpNorm]
  · intro x
    -- Zero detection combines `norm_eq_zero` with injectivity of `WithLp.toLp`.
    rw [lpNorm]
    exact
      ((norm_eq_zero : ‖WithLp.toLp p x‖ = 0 ↔ WithLp.toLp p x = 0).trans
        (WithLp.toLp_eq_zero (p := p) (x := x)))
  · intro a x
    -- Absolute homogeneity is the scalar rule for the ambient norm.
    simpa [lpNorm, Real.norm_eq_abs] using (norm_smul a (WithLp.toLp p x))
  · intro x y
    -- The triangle inequality is the ambient norm triangle inequality.
    simpa [lpNorm] using (norm_add_le (WithLp.toLp p x) (WithLp.toLp p y))

/-- The `ℓ^∞` norm on `ℝ^n`. -/
noncomputable def linftyNorm : (Fin n → ℝ) → ℝ :=
  lpNorm (⊤ : ENNReal)

/-- The `ℓ^1` norm on `ℝ^n`. -/
noncomputable def l1Norm : (Fin n → ℝ) → ℝ :=
  lpNorm (1 : ENNReal)

/-- The `ℓ^2` norm on `ℝ^n`. -/
noncomputable def l2Norm : (Fin n → ℝ) → ℝ :=
  lpNorm (2 : ENNReal)

notation3:max "‖" x "‖∞" => linftyNorm x
notation3:max "‖" x "‖₁" => l1Norm x
notation3:max "‖" x "‖₂" => l2Norm x

/-- For `n ≥ 1`, the `ℓ^∞` norm is the maximum of the coordinatewise absolute values. -/
theorem linftyNorm_eq_finset_sup'_abs [Nonempty (Fin n)] (x : Fin n → ℝ) :
    ‖x‖∞ = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |x i|) := by
  -- Rewrite the `PiLp` supremum formula as a finite maximum on `Fin n`.
  rw [Finset.sup'_univ_eq_ciSup]
  simpa [linftyNorm, lpNorm, Real.norm_eq_abs] using
    (PiLp.norm_eq_ciSup (WithLp.toLp (⊤ : ENNReal) x))

/-- The `ℓ^∞` norm is the supremum of the coordinatewise absolute values. -/
theorem linftyNorm_eq_iSup_abs (x : Fin n → ℝ) :
    ‖x‖∞ = ⨆ i : Fin n, |x i| := by
  -- Transport the canonical `PiLp` `iSup` formula back to coordinates.
  simpa [linftyNorm, lpNorm, Real.norm_eq_abs] using
    (PiLp.norm_eq_ciSup (WithLp.toLp (⊤ : ENNReal) x))

/-- The `ℓ^∞` norm is a vector norm on `ℝ^n`. -/
instance linftyNorm_isVectorNorm : IsVectorNorm (fun x : Fin n → ℝ ↦ ‖x‖∞) := by
  -- Specialize the general `ℓ^p` norm theorem to `p = ∞`.
  simpa [linftyNorm] using (lpNorm_isVectorNorm (p := (⊤ : ENNReal)))

/-- The `ℓ^1` norm is the sum of the coordinatewise absolute values. -/
theorem l1Norm_eq_sum_abs (x : Fin n → ℝ) :
    ‖x‖₁ = ∑ i : Fin n, |x i| := by
  -- Use the specialized `PiLp` formula for `p = 1`.
  simpa [l1Norm, lpNorm, Real.norm_eq_abs] using
    (PiLp.norm_eq_of_L1 (WithLp.toLp (1 : ENNReal) x))

/-- The `ℓ^1` norm is a vector norm on `ℝ^n`. -/
instance l1Norm_isVectorNorm : IsVectorNorm (fun x : Fin n → ℝ ↦ ‖x‖₁) := by
  -- Specialize the general `ℓ^p` norm theorem to `p = 1`.
  simpa [l1Norm] using (lpNorm_isVectorNorm (p := (1 : ENNReal)))

/-- The `ℓ^2` norm is the square root of the sum of the squared absolute values. -/
theorem l2Norm_eq_sqrt_sum_sq (x : Fin n → ℝ) :
    ‖x‖₂ = Real.sqrt (∑ i : Fin n, |x i| ^ (2 : ℕ)) := by
  -- Use the specialized `PiLp` formula for `p = 2`.
  simpa [l2Norm, lpNorm, Real.norm_eq_abs] using
    (PiLp.norm_eq_of_L2 (WithLp.toLp (2 : ENNReal) x))

/-- The `ℓ^2` norm is a vector norm on `ℝ^n`. -/
instance l2Norm_isVectorNorm : IsVectorNorm (fun x : Fin n → ℝ ↦ ‖x‖₂) := by
  -- Specialize the general `ℓ^p` norm theorem to `p = 2`.
  simpa [l2Norm] using (lpNorm_isVectorNorm (p := (2 : ENNReal)))

/-- The ellipsoid norm attached to a real square matrix `A`. For positive-definite `A`, the
corresponding theorem below upgrades it to a vector norm. -/
noncomputable def ellipsoidNorm (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x ↦ Real.sqrt (x ⬝ᵥ (A *ᵥ x))

/-- The ellipsoid norm is given by `sqrt (xᵀ A x)`. -/
theorem ellipsoidNorm_eq_sqrt_dotProduct_mulVec (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ellipsoidNorm A x = Real.sqrt (x ⬝ᵥ (A *ᵥ x)) :=
  rfl

/-- With `hA : A.PosDef`, the ellipsoid norm is a vector norm on `ℝ^n`. -/
theorem ellipsoidNorm_isVectorNorm (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsVectorNorm (ellipsoidNorm A) := by
  let normA : (Fin n → ℝ) → ℝ := (A.toNormedAddCommGroup hA).toNorm.norm
  have hnorm : ∀ x : Fin n → ℝ, ellipsoidNorm A x = normA x := by
    intro x
    -- Compare against the explicit norm field of the canonical matrix-induced owner.
    change ellipsoidNorm A x = (A.toNormedAddCommGroup hA).toNorm.norm x
    symm
    simpa [ellipsoidNorm, dotProduct_comm] using
      (show (A.toNormedAddCommGroup hA).toNorm.norm x = Real.sqrt ((A *ᵥ x) ⬝ᵥ x) by rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    -- Nonnegativity is inherited from the canonical norm attached to `A`.
    rw [hnorm x]
    simpa [normA] using
      (@norm_nonneg (Fin n → ℝ)
        ((A.toNormedAddCommGroup hA).toNormedAddGroup.toSeminormedAddGroup) x)
  · intro x
    -- Zero detection is inherited from the canonical norm attached to `A`.
    rw [hnorm x]
    simpa [normA] using
      (@norm_eq_zero (Fin n → ℝ) ((A.toNormedAddCommGroup hA).toNormedAddGroup) x)
  · intro a x
    -- Absolute homogeneity follows directly from the quadratic-form formula.
    calc
      ellipsoidNorm A (a • x)
          = Real.sqrt (a ^ 2 * (x ⬝ᵥ (A *ᵥ x))) := by
              simp [ellipsoidNorm, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
                pow_two, mul_assoc]
      _ = Real.sqrt (a ^ 2) * Real.sqrt (x ⬝ᵥ (A *ᵥ x)) := by
            rw [Real.sqrt_mul (sq_nonneg a)]
      _ = |a| * ellipsoidNorm A x := by
            rw [Real.sqrt_sq_eq_abs]
            simp [ellipsoidNorm]
  · intro x y
    -- The triangle inequality is inherited from the canonical norm attached to `A`.
    rw [hnorm (x + y), hnorm x, hnorm y]
    simpa [normA] using
      (@norm_add_le (Fin n → ℝ)
        ((A.toNormedAddCommGroup hA).toNormedAddGroup.toSeminormedAddGroup) x y)
