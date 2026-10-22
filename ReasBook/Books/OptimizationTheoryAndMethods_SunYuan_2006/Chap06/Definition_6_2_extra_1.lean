/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_12

noncomputable section

variable {n : ℕ}

-- Domain sampling for this item:
-- - primary domain: quadratic-over-affine conic models on Euclidean space;
-- - sampled project owner declarations: `quadraticFunction`,
--   `ConicTrustRegionSubproblem.admissibleSet`, `ConicTrustRegionSubproblem.objective`;
-- - sampled mathlib declarations: `AffineMap`, `Set.EqOn`, `ContDiffOn.div`;
-- - best owner abstraction: the conic ratio together with its admissible nonvanishing-denominator
--   domain, with domain-restricted recognition predicates derived from that owner;
-- - primitive data: the quadratic numerator coefficients `A`, `b`, `c` and the affine
--   denominator `a`;
-- - derived API: the admissible domain, the ambient conic ratio, and the domain-local predicate
--   `IsConicOn`.

-- Semantic recall: `lean_leansearch` surfaced only the homogeneous `QuadraticMap` API and
-- matrix conversions, while nearby repository precedent uses the explicit matrix/vector/scalar
-- formula for general quadratic functions. The source-facing notion therefore stays on that
-- concrete `ℝ^n` layer.

/-- The quadratic function `x ↦ xᵀ A x + bᵀ x + c` on `Point n = ℝ^n`. -/
def quadraticFunction (A : MatrixN n) (b : Point n) (c : ℝ) (x : Point n) : ℝ :=
  matrixQuadratic A x + dotProduct b x + c

/-- Evaluating `quadraticFunction A b c` expands to `xᵀ A x + bᵀ x + c`. -/
theorem quadraticFunction_apply (A : MatrixN n) (b : Point n) (c : ℝ) (x : Point n) :
    quadraticFunction A b c x = dotProduct x (A.mulVec x) + dotProduct b x + c := rfl

/-- The quadratic numerator `x ↦ xᵀ A x + bᵀ x + c` is smooth. -/
theorem quadraticFunction_contDiff (A : MatrixN n) (b : Point n) (c : ℝ) :
    ContDiff ℝ ⊤ (quadraticFunction A b c) := by
  let LA : Point n →L[ℝ] Point n := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hLA : ContDiff ℝ ⊤ LA := LA.contDiff
  have hquadratic' : ContDiff ℝ ⊤ (fun x : Point n ↦ (innerSL ℝ x) (LA x)) :=
    (innerSL ℝ).contDiff.clm_apply hLA
  have hquadratic : ContDiff ℝ ⊤ (fun x : Point n ↦ x ⬝ᵥ LA x) := by
    convert hquadratic' using 1
    funext x
    rw [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp
  have hlinear' : ContDiff ℝ ⊤ (fun x : Point n ↦ (innerSL ℝ b) x) := (innerSL ℝ b).contDiff
  have hlinear : ContDiff ℝ ⊤ (fun x : Point n ↦ b ⬝ᵥ x) := by
    convert hlinear' using 1
    funext x
    rw [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp
  have hconst : ContDiff ℝ ⊤ (fun _ : Point n ↦ c) := contDiff_const
  have hsum : ContDiff ℝ ⊤ (fun x : Point n ↦ x ⬝ᵥ LA x + b ⬝ᵥ x + c) :=
    hquadratic.add hlinear |>.add hconst
  convert hsum using 1
  funext x
  rfl

/-- An affine function on `Point n = ℝ^n` is smooth. -/
theorem contDiff_affineMap (a : Point n →ᵃ[ℝ] ℝ) : ContDiff ℝ ⊤ a := by
  let a' : Point n →ᴬ[ℝ] ℝ := { a with
    cont := a.continuous_of_finiteDimensional }
  change ContDiff ℝ ⊤ (fun x : Point n ↦ a' x)
  simpa using a'.contDiff

/-- The admissible domain of the conic ratio `quadraticFunction A b c / a^2` consists of the
points where the affine denominator does not vanish. -/
def conicDomain (a : Point n →ᵃ[ℝ] ℝ) : Set (Point n) :=
  { x | a x ≠ 0 }

/-- Membership in `conicDomain a` is exactly the nonvanishing condition `a x ≠ 0`. -/
theorem mem_conicDomain_iff (a : Point n →ᵃ[ℝ] ℝ) (x : Point n) :
    x ∈ conicDomain a ↔ a x ≠ 0 :=
  Iff.rfl

/-- The ambient quadratic-over-affine ratio attached to the numerator data `A`, `b`, `c` and the
affine denominator `a`. Its source-facing domain is `conicDomain a`. -/
def conicRatio (A : MatrixN n) (b : Point n) (c : ℝ) (a : Point n →ᵃ[ℝ] ℝ) (x : Point n) : ℝ :=
  quadraticFunction A b c x / (a x) ^ (2 : ℕ)

/-- Evaluating `conicRatio A b c a` expands to the quadratic-over-affine formula. -/
theorem conicRatio_apply
    (A : MatrixN n) (b : Point n) (c : ℝ) (a : Point n →ᵃ[ℝ] ℝ) (x : Point n) :
    conicRatio A b c a x = quadraticFunction A b c x / (a x) ^ (2 : ℕ) :=
  rfl

/-- The ambient conic ratio is smooth on its admissible domain `conicDomain a`. -/
theorem conicRatio_contDiffOn
    (A : MatrixN n) (b : Point n) (c : ℝ) (a : Point n →ᵃ[ℝ] ℝ) :
    ContDiffOn ℝ ⊤ (conicRatio A b c a) (conicDomain a) := by
  have hquadratic : ContDiffOn ℝ ⊤ (quadraticFunction A b c) (conicDomain a) :=
    (quadraticFunction_contDiff A b c).contDiffOn
  have haSq : ContDiffOn ℝ ⊤ (fun x : Point n ↦ (a x) ^ (2 : ℕ)) (conicDomain a) :=
    ((contDiff_affineMap a).pow 2).contDiffOn
  refine hquadratic.div haSq ?_
  intro x hx
  exact pow_ne_zero 2 hx

/-- Chapter06 Definition 6.2-extra-1: a function is conic on a domain `s` when, on that domain,
it agrees with a quadratic function divided by the square of an affine function whose denominator
does not vanish on `s`. -/
class IsConicOn (s : Set (Point n)) (f : Point n → ℝ) : Prop where
  exists_ratio :
    ∃ A : MatrixN n,
      ∃ b : Point n,
        ∃ c : ℝ,
          ∃ a : Point n →ᵃ[ℝ] ℝ,
            s ⊆ conicDomain a ∧ Set.EqOn f (conicRatio A b c a) s

/-- The predicate `IsConicOn` is proof-irrelevant. -/
instance isConicOnSubsingleton (s : Set (Point n)) (f : Point n → ℝ) :
    Subsingleton (IsConicOn s f) := inferInstance

/-- The canonical quadratic-over-affine ratio is conic on its natural admissible domain. -/
theorem isConicOn_conicDomain
    (A : MatrixN n) (b : Point n) (c : ℝ) (a : Point n →ᵃ[ℝ] ℝ) :
    IsConicOn (conicDomain a) (conicRatio A b c a) := by
  refine ⟨?_⟩
  exact ⟨A, b, c, a, subset_rfl, fun _ hx ↦ rfl⟩

/-- A function that is conic on `s` is smooth on `s`. -/
theorem IsConicOn.contDiffOn {s : Set (Point n)} {f : Point n → ℝ} (hf : IsConicOn s f) :
    ContDiffOn ℝ ⊤ f s := by
  rcases hf.exists_ratio with ⟨A, b, c, a, hs, hEq⟩
  exact ((conicRatio_contDiffOn A b c a).mono hs).congr (by
    intro x hx
    exact hEq hx)

/-- Being conic on `s` is equivalent to agreeing on `s` with a quadratic function divided by the
square of an affine function whose denominator does not vanish on `s`. -/
theorem isConicOn_iff (s : Set (Point n)) (f : Point n → ℝ) :
    IsConicOn s f ↔
      ∃ A : MatrixN n,
        ∃ b : Point n,
          ∃ c : ℝ,
            ∃ a : Point n →ᵃ[ℝ] ℝ,
              s ⊆ conicDomain a ∧ Set.EqOn f (conicRatio A b c a) s := by
  constructor
  · intro hf
    exact hf.exists_ratio
  · rintro ⟨A, b, c, a, hs, hEq⟩
    exact ⟨⟨A, b, c, a, hs, hEq⟩⟩
