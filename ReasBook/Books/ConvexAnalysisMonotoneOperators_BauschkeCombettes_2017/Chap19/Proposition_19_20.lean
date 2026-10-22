/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Corollary_19_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section Basic

variable {H : Type u} {K : Type v}
variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: both summands lie in `]-∞,+∞]`, and the sum of two values strictly above `-∞`
-- still lies in `]-∞,+∞]`.
private theorem compositePerturbationFunction_value_mem_Ioi_bot
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (p : H × K) :
    ((f p.1 : EReal) + (g (L p.1 + p.2) : EReal)) ∈ Set.Ioi (⊥ : EReal) := sorry

/-- The perturbation function `F(x,y) = f(x) + g(Lx + y)` attached to the composite objective
`x ↦ f(x) + g(Lx)`. -/
def compositePerturbationFunction
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    H × K → Set.Ioi (⊥ : EReal) :=
  fun p ↦
    ⟨(f p.1 : EReal) + (g (L p.1 + p.2) : EReal),
      compositePerturbationFunction_value_mem_Ioi_bot f g L p⟩

-- Proof sketch: unfold `compositePerturbationFunction`; coercing away from the subtype forgets
-- only the proof that the value is strictly above `-∞`.
/-- Evaluating `compositePerturbationFunction f g L` gives the formula
`f(x) + g(Lx + y)`. -/
@[simp] theorem compositePerturbationFunction_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (x : H) (y : K) :
    (compositePerturbationFunction f g L (x, y) : EReal) =
      (f x : EReal) + (g (L x + y) : EReal) :=
  rfl

-- Proof sketch: evaluate the perturbation function at `(x, 0)` and simplify the resulting
-- formula `g (L x + 0)` to `g (L x)`.
/-- Proposition 19.20 (2): the primal problem associated with the perturbation
`F(x,y) = f(x) + g(Lx + y)` is the minimization of `x ↦ f(x) + g(Lx)`. -/
theorem perturbationPrimalObjective_compositePerturbationFunction
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    perturbationPrimalObjective (compositePerturbationFunction f g L) =
      compositePrimalObjective f g L := by
  ext x
  simp [compositePrimalObjective]

end Basic

section ProductL2Ambient

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2
attribute [local instance] Classical.propDecidable

-- Proof sketch: the map `(x, y) ↦ Lx + y` is continuous and affine on `H × K`, so composing `g`
-- with it preserves lower semicontinuity and convexity; adding the pullback of `f` preserves
-- both properties. Properness is automatic because `hf` and `hg` give points `x ∈ dom f` and
-- `z ∈ dom g`, and then choosing `y := z - Lx` makes the perturbation finite at `(x, y)`.
/-- Proposition 19.20 (1): if `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, then the perturbation
`F(x,y) = f(x) + g(Lx + y)` belongs to `Γ₀(ℋ ⊕ 𝒦)`. -/
theorem compositePerturbationFunction_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) :
    compositePerturbationFunction f g L ∈ Γ₀(H × K) := sorry

-- Proof sketch: unfold `perturbationDualObjective` for the perturbation,
-- `z = Lx + y`,
-- and recognize the remaining supremum as `f^*(-L^* v) + g^*(v)`.
/-- Proposition 19.20 (3): the dual problem associated with the perturbation
`F(x,y) = f(x) + g(Lx + y)` is the minimization of
`v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem perturbationDualObjective_compositePerturbationFunction
    [CompleteSpace H] [CompleteSpace K]
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    perturbationDualObjective (compositePerturbationFunction f g L) =
      compositeDualObjective f g L := sorry

-- Proof sketch: unfold `lagrangian` for the perturbation function, change variables
-- `z = Lx + y`, and identify the remaining infimum with `-g^*(v)`. The cases `x ∉ dom f` and
-- `v ∉ dom g^*` produce the values `+∞` and `-∞`, respectively.
/-- Proposition 19.20 (4): the Lagrangian of the perturbation `F(x,y) = f(x) + g(Lx + y)` is the
piecewise function from formula `(19.34)`. -/
theorem lagrangian_compositePerturbationFunction
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (x : H) (v : K) :
    ℒ[compositePerturbationFunction f g L] x v =
      if hx : x ∈ effectiveDomain f then
        if hv : v ∈ effectiveDomain (g∗[hg]) then
          (f x : EReal) + (⟪L x, v⟫_ℝ : EReal) - (g∗[hg] v : EReal)
        else
          ⊥
      else
        ⊤ := sorry

section ParametricDuality

variable [CompleteSpace H] [CompleteSpace K]

-- Proof sketch: Proposition 19.20 (1) places the perturbation in `Γ₀(H × K)`. Corollary 19.19
-- then identifies saddle points of its Lagrangian with primal-dual solution pairs, while
-- Theorem 19.1 and Corollary 16.30 rewrite those primal-dual optimality conditions as
-- `-L^* v ∈ ∂ f(x)` and `Lx ∈ ∂ g^*(v)`.
/-- Proposition 19.20 (5): assuming the primal and dual optimal values satisfy
`μ = -μ* ∈ ℝ`, a pair `(x, v)` is a saddle point of the Lagrangian if and only if
`-L^* v ∈ ∂ f(x)` and `Lx ∈ ∂ g^*(v)`. -/
theorem isSaddlePointOn_lagrangian_compositePerturbationFunction_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hμ :
      ∃ μ : ℝ,
        compositePrimalOptimalValue f g L = μ ∧
          compositeDualOptimalValue f g L = -μ)
    (x : H) (v : K) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[compositePerturbationFunction f g L]) x v ↔
      -L.adjoint v ∈ (∂ f) x ∧
        L x ∈ (∂ (g∗[hg])) v := sorry

end ParametricDuality

end ProductL2Ambient

end

end ERealFunction
