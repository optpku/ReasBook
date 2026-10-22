/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef

public section

noncomputable section

namespace Matrix

universe u

section Inner

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The `A`-energy inner product on `EuclideanSpace ℝ n`, defined from the canonical
inner-product-space structure induced by the positive-semidefinite matrix `A`. -/
def energyInner (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (f₁ f₂ : EuclideanSpace ℝ n) : ℝ :=
  (A.toInnerProductSpace hA).inner (fun i ↦ f₁ i) (fun i ↦ f₂ i)

end Inner

section Norm

variable {n : Type u} [Fintype n]

/-- The `A`-energy norm on `EuclideanSpace ℝ n`, defined from the canonical norm induced by
the positive-definite matrix `A`. -/
def energyNorm (A : Matrix n n ℝ) (hA : A.PosDef) (f : EuclideanSpace ℝ n) : ℝ :=
  (A.toNormedAddCommGroup hA).norm (fun i ↦ f i)

end Norm

namespace Energy

/-- Scoped notation for the `A`-energy inner product `⟪f₁, f₂⟫_[A, hA]`. -/
scoped notation "⟪" f₁ ", " f₂ "⟫_[" A ", " hA "]" =>
  Matrix.energyInner A hA f₁ f₂

/-- Scoped notation for the `A`-energy norm `‖f‖_[A, hA]`. -/
scoped notation:max "‖" f "‖_[" A ", " hA "]" =>
  Matrix.energyNorm A hA f

end Energy

open scoped Matrix.Energy

section InnerFacts

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The `A`-energy inner product agrees with `inner ℝ (A.toEuclideanLin f₁) f₂`.
-/
theorem energyInner_eq (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (f₁ f₂ : EuclideanSpace ℝ n) :
    ⟪f₁, f₂⟫_[A, hA] = inner ℝ (A.toEuclideanLin f₁) f₂ := by
  have htoEuclidean :
      (A.toEuclideanLin f₂).ofLp = A *ᵥ f₂.ofLp := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLin'_apply] using
      (Matrix.ofLp_toLpLin (p := 2) (q := 2) A f₂)
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  -- Identify the induced inner product with `⟪f₁, A f₂⟫` and use self-adjointness of `A`.
  calc
    ⟪f₁, f₂⟫_[A, hA] = inner ℝ f₁ (A.toEuclideanLin f₂) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, htoEuclidean]
      rfl
    _ = inner ℝ (A.toEuclideanLin f₁) f₂ := by
      symm
      exact hsymm f₁ f₂

end InnerFacts

section NormFacts

variable {n : Type u} [Fintype n]

/-- The `A`-energy norm is the square root of the `A`-energy inner product of a
vector with itself. -/
theorem energyNorm_eq_sqrt_energyInner (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    ‖f‖_[A, hA] = Real.sqrt ⟪f, f⟫_[A, hA.posSemidef] := by
  -- This is the defining relation for the norm induced by `A`.
  rfl

end NormFacts

end Matrix
