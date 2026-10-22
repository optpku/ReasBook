/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Corollary_19_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

attribute [local instance] Classical.propDecidable

section Basic

variable {H : Type u} {K : Type v}

-- Proof sketch: specialize the canonical indicator owner `ι[C]` to the singleton `{r}`.
/-- Coercing the canonical singleton indicator `ι[{r}]` to `EReal` gives the expected piecewise
formula. -/
@[simp] theorem indicator_singleton_apply
    (r : K) (y : K) :
    (ι[{r}] y : EReal) = if y = r then (0 : EReal) else ⊤ := sorry

/-- The perturbation function attached to minimizing `f` subject to the equality constraint
`L x = r`, obtained by specializing the canonical composite perturbation to the singleton
indicator `ι[{r}]`. -/
def equalityConstraintPerturbationFunction
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [SeminormedAddCommGroup K] [NormedSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) :
    H × K → Set.Ioi (⊥ : EReal) :=
  compositePerturbationFunction f (ι[{r}]) L

-- Proof sketch: unfold `equalityConstraintPerturbationFunction` as the composite perturbation
-- with `g = ι_{ {r} }`; the singleton indicator is `0` exactly when `L x + y = r`,
-- equivalently `L x = r - y`, and is `⊤` otherwise.
/-- Evaluating the equality-constraint perturbation function gives the piecewise formula from
Proposition 19.21. -/
@[simp] theorem equalityConstraintPerturbationFunction_apply
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [SeminormedAddCommGroup K] [NormedSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) (x : H) (y : K) :
    (equalityConstraintPerturbationFunction f L r (x, y) : EReal) =
      if L x = r - y then (f x : EReal) else ⊤ := sorry

-- Proof sketch: specialize the canonical effective-domain formula for `ι[C]` to the singleton
-- `{r}`.
/-- The effective domain of the singleton indicator is the singleton itself. -/
@[simp] theorem effectiveDomain_indicator_singleton
    (r : K) :
    effectiveDomain (ι[{r}]) = ({r} : Set K) := sorry

-- Proof sketch: evaluate `perturbationPrimalObjective` at the zero perturbation and simplify the
-- singleton indicator term at `L x`, which vanishes exactly when `L x = r`.
/-- Proposition 19.21 (2): the primal problem attached to the equality-constraint perturbation is
the constrained minimization of `f` over `L ⁻¹' {r}`. -/
theorem perturbationPrimalObjective_equalityConstraintPerturbationFunction
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [SeminormedAddCommGroup K] [NormedSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) :
    perturbationPrimalObjective (equalityConstraintPerturbationFunction f L r) =
      fun x : H ↦ if L x = r then (f x : EReal) else ⊤ := sorry

end Basic

section InnerProduct

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

-- Proof sketch: a singleton in a real Hilbert space is nonempty, closed, and convex, so its
-- indicator is proper, lower semicontinuous, and convex.
/-- The indicator of a singleton belongs to `Γ₀`. -/
theorem indicator_singleton_mem_gammaZero
    (r : K) :
    ι[{r}] ∈ Γ₀(K) := sorry

-- Proof sketch: the Fenchel conjugate of the indicator of a set is its support function, and the
-- support function of the singleton `{r}` is the linear functional `v ↦ ⟪v, r⟫`.
/-- The conjugate of the singleton indicator is the linear functional `v ↦ ⟪v, r⟫`. -/
@[simp] theorem conjugate_indicator_singleton
    (r : K) (v : K) :
    conjugate (fun y : K ↦ (ι[{r}] y : EReal)) v =
      (⟪v, r⟫_ℝ : EReal) := sorry

-- Proof sketch: identify the conjugate of the singleton indicator with the continuous linear
-- functional `v ↦ ⟪v, r⟫`, whose subdifferential is the singleton `{r}` at every point.
/-- A vector belongs to the subdifferential of the conjugate of the singleton indicator exactly
when it equals the singleton point. -/
@[simp] theorem mem_subdifferential_gammaZeroConjugate_indicator_singleton_iff
    (r : K) (x : K) (v : K) :
    x ∈ (∂ (ι[{r}]∗[indicator_singleton_mem_gammaZero r])) v ↔
      x = r := sorry

-- Proof sketch: identify the equality-constraint perturbation with the singleton-indicator
-- composite perturbation, then specialize Proposition 19.20 (4) and simplify the
-- conjugate term to `⟪v, r⟫`, so the Lagrangian becomes `f x + ⟪L x - r, v⟫` on `dom f`.
/-- Proposition 19.21 (4): the Lagrangian is the piecewise map
`(x, v) ↦ f x + ⟪L x - r, v⟫` on the effective domain of `f`, and `+∞` outside it. -/
theorem lagrangian_equalityConstraintPerturbationFunction
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) (x : H) (v : K) :
    ℒ[equalityConstraintPerturbationFunction f L r] x v =
      if hx : x ∈ effectiveDomain f then
        (f x : EReal) + (⟪L x - r, v⟫_ℝ : EReal)
      else
        ⊤ := sorry

end InnerProduct

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

-- Proof sketch: specialize Proposition 19.20 (1) to the singleton indicator `ι_{ {r} }`.
-- The domain-intersection hypothesis becomes `r ∈ L '' effectiveDomain f` because the effective
-- domain of the singleton indicator is `{r}`.
/-- Proposition 19.21 (1): if `f ∈ Γ₀(ℋ)` and `r ∈ L (dom f)`, then the equality-constraint
perturbation function belongs to `Γ₀(ℋ ⊕ 𝒦)`. -/
theorem equalityConstraintPerturbationFunction_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K)
    (hr : r ∈ L '' effectiveDomain f) :
    equalityConstraintPerturbationFunction f L r ∈ Γ₀(H × K) := sorry

end ProductL2Ambient

section CompleteDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: identify the equality-constraint perturbation with the composite perturbation for
-- the singleton indicator, then specialize the dual formula from Proposition 19.20 and rewrite the
-- conjugate as `v ↦ ⟪v, r⟫`.
/-- Proposition 19.21 (3): the dual problem is
`v ↦ f^*(-L^* v) + ⟪v, r⟫`. -/
theorem perturbationDualObjective_equalityConstraintPerturbationFunction
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (r : K) :
    perturbationDualObjective (equalityConstraintPerturbationFunction f L r) =
      fun v : K ↦
        conjugate (fun x : H ↦ (f x : EReal)) (-L.adjoint v) + (⟪v, r⟫_ℝ : EReal) := sorry

-- Proof sketch: identify the equality-constraint perturbation with the singleton-indicator
-- composite perturbation and specialize Proposition 19.20 (5). Then rewrite the
-- second subdifferential condition using that the conjugate of the singleton indicator has
-- singleton subdifferential `{r}`.
/-- Proposition 19.21 (5): under strong duality, `(x, v)` is a saddle point of the Lagrangian if
and only if it satisfies the corresponding saddle-point optimality system. -/
theorem isSaddlePointOn_lagrangian_equalityConstraintPerturbationFunction_iff
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K)
    (hr : r ∈ L '' effectiveDomain f)
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective (equalityConstraintPerturbationFunction f L r))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective (equalityConstraintPerturbationFunction f L r))) = -μ)
    (x : H) (v : K) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbationFunction f L r]) x v ↔
      -L.adjoint v ∈ (∂ f) x ∧
        L x = r := sorry

-- Proof sketch: Proposition 19.21 (5) turns a saddle point into primal optimality for the
-- equality-constrained problem, and Corollary 19.19 identifies the saddle value with the primal
-- optimum `F (x, 0) = f x`.
/-- Proposition 19.21 (6): at a saddle point, `f x` equals the optimal primal value of the
equality-constrained problem. -/
theorem
    value_eq_perturbationPrimalObjective_sInf_of_isSaddlePointOn_equalityConstraintPerturbation
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K)
    (hr : r ∈ L '' effectiveDomain f)
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective (equalityConstraintPerturbationFunction f L r))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective (equalityConstraintPerturbationFunction f L r))) = -μ)
    {x : H} {v : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbationFunction f L r]) x v) :
    (f x : EReal) =
      sInf
        (Set.range
          (perturbationPrimalObjective (equalityConstraintPerturbationFunction f L r))) := sorry

-- Proof sketch: Corollary 19.19 together with Proposition 19.17 identifies the saddle value with
-- the infimum of the Lagrangian fiber `z ↦ 𝓛(z, v)`, and the equality constraint gives
-- `F (x, 0) = f x`.
/-- Proposition 19.21 (7): at a saddle point, `f x` also equals the infimum of the Lagrangian
fiber `z ↦ 𝓛(z, v)`. -/
theorem
    value_eq_lagrangian_sInf_of_isSaddlePointOn_equalityConstraintPerturbation
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K)
    (hr : r ∈ L '' effectiveDomain f)
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective (equalityConstraintPerturbationFunction f L r))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective (equalityConstraintPerturbationFunction f L r))) = -μ)
    {x : H} {v : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbationFunction f L r]) x v) :
    (f x : EReal) =
      sInf (Set.range fun z : H ↦
        ℒ[equalityConstraintPerturbationFunction f L r] z v) := sorry

end CompleteDuality

end

end ERealFunction
