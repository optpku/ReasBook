/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace ERealFunction

section Primal

variable {H : Type u} {K : Type v}
variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup K] [NormedSpace ℝ K]

/-- The objective function of the primal composite problem associated with `f`, `g`, and `L`.
It is the canonical pointwise sum of `f.asEReal` and the pulled-back penalty `(g ∘ L).asEReal`. -/
def compositePrimalObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    H → EReal :=
  primalObjective f (g ∘ L)

/-- Evaluating the composite primal objective gives the value `f(x) + g(Lx)`. -/
@[simp] theorem compositePrimalObjective_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (x : H) :
    compositePrimalObjective f g L x = (f x : EReal) + (g (L x) : EReal) := by
  simp [compositePrimalObjective]

/-- The primal optimal value of the composite problem, defined as the infimum of the primal
objective range. -/
def compositePrimalOptimalValue
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    EReal :=
  primalOptimalValue f (g ∘ L)

/-- The composite primal optimal value is the infimum of the range of the composite primal
objective. -/
theorem compositePrimalOptimalValue_def
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositePrimalOptimalValue f g L = sInf (Set.range (compositePrimalObjective f g L)) := by
  rw [compositePrimalOptimalValue, primalOptimalValue_def, compositePrimalObjective]

end Primal

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

section

variable [CompleteSpace H] [CompleteSpace K]

/-- The objective function of the dual composite problem associated with `f`, `g`, and `L`. -/
def compositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    K → EReal :=
  f.asEReal∗ᵛ ∘ L.adjoint + g.asEReal∗

/-- The composite dual objective is the sum of the reflected conjugate of `f`, pulled back along
`L.adjoint`, and the conjugate of `g`. -/
@[simp] theorem compositeDualObjective_eq_add_reflectedConjugates
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositeDualObjective f g L = f.asEReal∗ᵛ ∘ L.adjoint + g.asEReal∗ := rfl

/-- Evaluating the composite dual objective gives the value `f^*(-L^*v) + g^*(v)`. -/
@[simp] theorem compositeDualObjective_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (v : K) :
    compositeDualObjective f g L v =
      f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v := rfl

/-- The dual optimal value of the composite problem, defined as the infimum of the dual objective
range. -/
def compositeDualOptimalValue
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    EReal :=
  sInf (Set.range (compositeDualObjective f g L))

/-- The composite dual optimal value is the infimum of the range of the composite dual
objective. -/
theorem compositeDualOptimalValue_def
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositeDualOptimalValue f g L = sInf (Set.range (compositeDualObjective f g L)) := rfl

/-- Definition 15.19: for the primal problem `min_x f(x) + g(Lx)` and the dual problem
`min_v f^*(-L^*v) + g^*(v)`, the duality gap is `0` in the exceptional case
`μ = -μ* ∈ {±∞}` and otherwise equals `μ + μ*`. -/
def compositeDualityGap
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    EReal :=
  if compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L ∧
      (compositePrimalOptimalValue f g L = (⊥ : EReal) ∨
        compositePrimalOptimalValue f g L = ⊤) then
    0
  else
    compositePrimalOptimalValue f g L + compositeDualOptimalValue f g L

/-- The composite duality gap is given by the case split from Definition 15.19. -/
theorem compositeDualityGap_def
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositeDualityGap f g L =
      if compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L ∧
          (compositePrimalOptimalValue f g L = (⊥ : EReal) ∨
            compositePrimalOptimalValue f g L = ⊤) then
        0
      else
        compositePrimalOptimalValue f g L + compositeDualOptimalValue f g L := rfl

end

end FenchelRockafellarDuality

end ERealFunction
