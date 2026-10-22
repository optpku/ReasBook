/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Exercise_11_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.EuclideanSubgradient

noncomputable section

section

variable {n m : ℕ}

open Chapter14 (IsSubgradientAt Point)
open scoped Subgradient

-- Layer triage:
-- * source-facing: `CuttingPlaneMethod`, `isCuttingPlaneSubproblemSolution`
-- * core/canonical: `linearlyConstrainedPolyhedron`, `subdifferential`, `IsMaxOn`, `Prod.fst`
-- * bridge/view: `IsSubgradientAt`, `isCuttingPlaneSubproblemSolution_iff`

/-- `IsPolyhedralSet S` means that the feasible set `S` admits some finite half-space
presentation `S = {x | Aᵀ x ≥ b}`. This keeps the source-facing owner as the set `S` while
recording the polyhedrality assumption required by Algorithm 14.4.1. -/
def IsPolyhedralSet (S : Set (Point n)) : Prop :=
  ∃ m' : ℕ,
    ∃ A : Matrix (Fin n) (Fin m') ℝ,
      ∃ b : Point m',
        S = linearlyConstrainedPolyhedron A b

/-- Unfolding `IsPolyhedralSet S` gives a finite half-space presentation of `S`. -/
theorem isPolyhedralSet_iff
    (S : Set (Point n)) :
    IsPolyhedralSet S ↔
      ∃ m' : ℕ,
        ∃ A : Matrix (Fin n) (Fin m') ℝ,
          ∃ b : Point m',
            S = linearlyConstrainedPolyhedron A b :=
  Iff.rfl

/-- The affine minorant of `f` at `x` determined by the chosen subgradient `g`. -/
def cuttingPlaneAffineMinorant
    (f : Point n → ℝ) (x g y : Point n) : ℝ :=
  f x + inner ℝ g (y - x)

/-- Unfolding `cuttingPlaneAffineMinorant f x g y` gives the source affine cut
`f(x) + ⟪g, y - x⟫`. -/
theorem cuttingPlaneAffineMinorant_apply
    (f : Point n → ℝ) (x g y : Point n) :
    cuttingPlaneAffineMinorant f x g y = f x + inner ℝ g (y - x) :=
  rfl

/-- The feasible region of the Step-3 cutting-plane linear program at stage `k`: the pair
`(v, y)` has `y ∈ S`, and `v` lies below every affine cut generated from the previous iterates
`x_i` and chosen subgradients `g_i` for `1 ≤ i ≤ k`. -/
def cuttingPlaneSubproblemFeasibleSet
    (f : Point n → ℝ) (S : Set (Point n)) (x g : ℕ → Point n) (k : ℕ) :
    Set (ℝ × Point n) :=
  {p |
    p.2 ∈ S ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ k →
        p.1 ≤ cuttingPlaneAffineMinorant f (x i) (g i) p.2}

/-- Membership in `cuttingPlaneSubproblemFeasibleSet f S x g k` is exactly the Step-3 LP
constraint system for the pair `(v, y)`. -/
theorem mem_cuttingPlaneSubproblemFeasibleSet_iff
    (f : Point n → ℝ) (S : Set (Point n)) (x g : ℕ → Point n) (k : ℕ)
    (v : ℝ) (y : Point n) :
    (v, y) ∈ cuttingPlaneSubproblemFeasibleSet f S x g k ↔
      y ∈ S ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ k →
          v ≤ cuttingPlaneAffineMinorant f (x i) (g i) y :=
  Iff.rfl

/-- `isCuttingPlaneSubproblemSolution f S x g k v y` means that `(v, y)` is feasible for the
Step-3 linear program at stage `k` and maximizes `v` on the feasible set cut out by the first
`k` subgradient affine minorants over `S`. The maximized owner is the canonical projection
`Prod.fst : ℝ × Point → ℝ`. -/
def isCuttingPlaneSubproblemSolution
    (f : Point n → ℝ) (S : Set (Point n)) (x g : ℕ → Point n) (k : ℕ)
    (v : ℝ) (y : Point n) :
    Prop :=
  (v, y) ∈ cuttingPlaneSubproblemFeasibleSet f S x g k ∧
    IsMaxOn Prod.fst
      (cuttingPlaneSubproblemFeasibleSet f S x g k)
      (v, y)

/-- Unfolding `isCuttingPlaneSubproblemSolution f S x g k v y` gives the source-feasibility
condition together with the canonical `IsMaxOn` surface for the Step-3 linear program. -/
theorem isCuttingPlaneSubproblemSolution_iff
    (f : Point n → ℝ) (S : Set (Point n)) (x g : ℕ → Point n) (k : ℕ)
    (v : ℝ) (y : Point n) :
    isCuttingPlaneSubproblemSolution f S x g k v y ↔
      (v, y) ∈ cuttingPlaneSubproblemFeasibleSet f S x g k ∧
        IsMaxOn Prod.fst
          (cuttingPlaneSubproblemFeasibleSet f S x g k)
          (v, y) :=
  Iff.rfl

/-- Chapter14 Algorithm 14.4.1: the cutting-plane method for a convex objective `f : ℝ^n → ℝ`
on a given polyhedral set `S` starts from an initial point `x₁ ∈ S`. For each stage `k ≥ 1`, it
records the current iterate `x_k`, a chosen subgradient vector `g_k ∈ ∂ f(x_k)` in the chapter's
Euclidean owner sense `IsSubgradientAt`, and the lower-model value `v_(k+1)` together
with the next iterate `x_(k+1)`
obtained by solving the Step-3 linear program over the first `k` affine cuts. -/
structure CuttingPlaneMethod (n : ℕ) where
  objective : Point n → ℝ
  feasibleSet : Set (Point n)
  objective_convex : ConvexOn ℝ Set.univ objective
  feasibleSet_polyhedral : IsPolyhedralSet feasibleSet
  initialPoint : Point n
  iterate : ℕ → Point n
  subgradient : ℕ → Point n
  lowerValue : ℕ → ℝ
  iterate_one : iterate 1 = initialPoint
  initialPoint_mem : initialPoint ∈ feasibleSet
  subgradient_mem {k : ℕ} (hk : 1 ≤ k) :
    IsSubgradientAt objective (iterate k) (subgradient k)
  linearProgram_step {k : ℕ} (hk : 1 ≤ k) :
    isCuttingPlaneSubproblemSolution
      objective
      feasibleSet
      iterate
      subgradient
      k
      (lowerValue (k + 1))
      (iterate (k + 1))

namespace CuttingPlaneMethod

/-- A cutting-plane method can be evaluated at stage `k` as its iterate `x_k`. -/
instance : CoeFun (CuttingPlaneMethod n) (fun _ ↦ ℕ → Point n) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : CuttingPlaneMethod n) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The Step-3 solution pair recorded at stage `k` is `(v_(k+1), x_(k+1))`. -/
def solutionPairAt (method : CuttingPlaneMethod n) (k : ℕ) : ℝ × Point n :=
  (method.lowerValue (k + 1), method.iterate (k + 1))

/-- Unfolding `method.solutionPairAt k` gives the recorded Step-3 solution pair
`(v_(k+1), x_(k+1))`. -/
theorem solutionPairAt_eq
    (method : CuttingPlaneMethod n) (k : ℕ) :
    method.solutionPairAt k = (method.lowerValue (k + 1), method.iterate (k + 1)) :=
  rfl

/-- At every stage `k ≥ 1`, the chosen vector `g_k` is a Euclidean subgradient of
`method.objective` at `x_k` in the chapter's canonical owner `IsSubgradientAt`. -/
theorem subgradient_mem_at
    (method : CuttingPlaneMethod n) {k : ℕ} (hk : 1 ≤ k) :
    IsSubgradientAt method.objective (method.iterate k) (method.subgradient k) :=
  method.subgradient_mem hk

/-- If `k ≥ 1`, the recorded pair `(v_(k+1), x_(k+1))` solves the Step-3 cutting-plane linear
program determined by the first `k` affine cuts. -/
theorem linearProgram_step_at
    (method : CuttingPlaneMethod n) {k : ℕ} (hk : 1 ≤ k) :
    isCuttingPlaneSubproblemSolution
      method.objective
      method.feasibleSet
      method.iterate
      method.subgradient
      k
      (method.lowerValue (k + 1))
      (method.iterate (k + 1)) :=
  method.linearProgram_step hk

/-- If `k ≥ 1`, the next iterate `x_(k+1)` remains in the feasible set `S`. -/
theorem iterate_succ_mem_feasibleSet
    (method : CuttingPlaneMethod n) {k : ℕ} (hk : 1 ≤ k) :
    method.iterate (k + 1) ∈ method.feasibleSet :=
  (method.linearProgram_step_at hk).1.1

/-- The optimal value `f*` of a cutting-plane method is the infimum of the objective on its
feasible set `S`. -/
def optimalValue (method : CuttingPlaneMethod n) : ℝ :=
  sInf (method.objective '' method.feasibleSet)

/-- Unfolding `method.optimalValue` gives the source quantity `f* = inf_{x ∈ S} f(x)`. -/
theorem optimalValue_eq_sInf_image
    (method : CuttingPlaneMethod n) :
    method.optimalValue = sInf (method.objective '' method.feasibleSet) :=
  rfl

end CuttingPlaneMethod

#print axioms linearlyConstrainedPolyhedron
#print axioms cuttingPlaneAffineMinorant
#print axioms cuttingPlaneSubproblemFeasibleSet
#print axioms CuttingPlaneMethod.optimalValue

end
