/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise

universe u

noncomputable section

variable {H : Type u} [NormedAddCommGroup H]

private def chebyshevCenterSqDist (x : H) : H → EReal :=
  fun y ↦ ((‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- The Chebyshev-center objective of a nonempty subset `C` is the canonical `]-∞,+∞]`-valued
supremum of the squared distances from `x` to points of `C`. -/
noncomputable def chebyshevCenterObjective (C : Set H) (hC_nonempty : C.Nonempty) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ by
    refine ⟨sSup (chebyshevCenterSqDist x '' C), ?_⟩
    rcases hC_nonempty with ⟨y, hy⟩
    exact lt_of_lt_of_le (EReal.bot_lt_coe _) <| (isLUB_sSup _).1 ⟨y, hy, rfl⟩

/-- Expanding the Chebyshev-center objective gives the supremum of the squared-distance image. -/
@[simp] theorem chebyshevCenterObjective_eq_sSup_sqDist
    (C : Set H) (hC_nonempty : C.Nonempty) (x : H) :
    (chebyshevCenterObjective C hC_nonempty x : EReal) = sSup (chebyshevCenterSqDist x '' C) :=
  rfl

/-- The active farthest-point map for the Chebyshev-center objective sends `x` to the points of
`C` that attain the supremal squared distance from `x`. -/
def chebyshevCenterActiveSet (C : Set H) : SetValuedOperator H H :=
  fun x ↦ {r | r ∈ C ∧ IsMaxOn (chebyshevCenterSqDist x) C r}

notation "Φ[" C "]" => chebyshevCenterActiveSet C

variable {C : Set H}

/-- A point belongs to the active farthest-point set exactly when it lies in `C` and realizes the
Chebyshev-center objective at `x`. -/
@[simp] theorem mem_chebyshevCenterActiveSet_iff
    (C : Set H) (hC_nonempty : C.Nonempty) (x r : H) :
    r ∈ Φ[C] x ↔
      r ∈ C ∧
        (((‖x - r‖ ^ (2 : ℕ) : ℝ) : EReal) = chebyshevCenterObjective C hC_nonempty x) := by
  sorry

-- Proof sketch: compactness makes the squared-distance map attain its supremum on `C`, and the
-- maximum-value function of the continuous family `(x, y) ↦ ‖x - y‖²` varies continuously with
-- `x`.
/-- Proposition 17.25 (1): clause (i). For a nonempty compact set, the finite real representative
of the Chebyshev-center objective is continuous. -/
theorem continuous_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) :
    Continuous fun x ↦ (chebyshevCenterObjective C hC_nonempty x : EReal).toReal := sorry

section InnerProduct

variable [InnerProductSpace ℝ H]

-- The next three clauses concern only the objective owner `chebyshevCenterObjective`; unlike the
-- active-set layer below, they do not require compactness or pointwise farthest-point attainment.
-- Proof sketch: write the objective as `x ↦ sup_{y ∈ C} (‖x - y‖²)`. Every function
-- `x ↦ ‖x - y‖²` is strongly convex with constant `2`, and the pointwise supremum of functions
-- with the same strong-convexity modulus preserves that modulus. Boundedness keeps the supremum
-- finite everywhere, so the canonical owner has nonempty effective domain.
/-- Proposition 17.25 (2): clause (i). For a nonempty bounded set, the Chebyshev-center objective
is strongly convex with constant `2`. -/
theorem stronglyConvex_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ERealFunction.StronglyConvex (chebyshevCenterObjective C hC_nonempty) 2 := sorry

-- Proof sketch: the previous clause gives strong convexity with constant `2`, and the objective is
-- lower semicontinuous as a pointwise supremum of continuous squared-distance functions; Corollary
-- 11.17 then turns that strong convexity into supercoercivity.
/-- Proposition 17.25 (3): clause (i). For a nonempty bounded set, the Chebyshev-center objective
is supercoercive. -/
theorem supercoercive_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ERealFunction.Supercoercive (chebyshevCenterObjective C hC_nonempty).asEReal := sorry

end InnerProduct

-- Proof sketch: for each `x`, compactness of `C` makes the squared-distance function attain its
-- maximum, so `Φ[C] x` is nonempty.
/-- Proposition 17.25 (4): clause (ii). The active farthest-point map is defined at every point of
the ambient space. -/
theorem dom_chebyshevCenterActiveSet_eq_univ
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) :
    (Φ[C]).dom = Set.univ := sorry

-- Proof sketch: if `(xₙ, rₙ) → (x, r)` with each `rₙ ∈ Φ[C] xₙ`, then compactness makes `C`
-- closed, so `r ∈ C`; continuity of the objective and of the squared norm then passes the
-- equality `‖xₙ - rₙ‖² = chebyshevCenterObjective C xₙ` to the limit.
/-- Proposition 17.25 (5): clause (ii). The graph of the active farthest-point map is closed. -/
theorem isClosed_graph_chebyshevCenterActiveSet
    (hCcompact : IsCompact C) :
    IsClosed ((Φ[C]).graph) := sorry

-- Proof sketch: each value `Φ[C] x` is a closed subset of the compact set `C`, hence compact.
/-- Proposition 17.25 (6): clause (ii). Every active farthest-point value set is compact. -/
theorem isCompact_chebyshevCenterActiveSet_value
    (hCcompact : IsCompact C) (x : H) :
    IsCompact (Φ[C] x) := sorry

section InnerProduct

variable [InnerProductSpace ℝ H]

-- Proof sketch: for `r ∈ Φ[C] x`, the pointwise lower estimate comes from comparing the objective
-- at `x + t z` with the single witness `r`. For the reverse inequality, choose maximizers
-- `rₙ ∈ Φ[C] (x + tₙ z)` along a vanishing positive sequence `tₙ → 0`, extract a convergent
-- subsequence from compactness of `C`, and pass to the limit.
/-- Proposition 17.25 (7): clause (iii). The directional derivative of the Chebyshev-center
objective is the support function of the pointwise scaled active displacement set
`2 • ({x} - Φ[C] x)`, equivalently twice the maximal pairing with the active farthest-point
displacements. -/
theorem directionalDerivative_chebyshevCenterObjective_eq_supportFunction_activeDisplacements
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x z : H) :
    (chebyshevCenterObjective C hC_nonempty)′(x; z) =
      σ[(2 : ℝ) • (({x} : Set H) - Φ[C] x)] z := sorry

-- Proof sketch: rewrite the previous clause as a support-function identity for the pointwise
-- scaled displacement set `2 • ({x} - Φ[C] x)`, then apply Proposition 17.24 to identify the
-- subdifferential with the closed convex hull of that active displacement set.
/-- Proposition 17.25 (8): clause (iv). The subdifferential of the Chebyshev-center objective is
the pointwise scaled translate `2 • ({x} - closedConvexHull ℝ (Φ[C] x))` of the closed convex
hull of the active farthest-point set. -/
theorem subdifferential_chebyshevCenterObjective_eq_smul_sub_closedConvexHull_activeSet
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (x : H) :
    (∂ (chebyshevCenterObjective C hC_nonempty)) x =
      (2 : ℝ) • (({x} : Set H) - closedConvexHull ℝ (Φ[C] x)) := sorry

/-- Proposition 17.25 (10): clause (v). A point minimizes the Chebyshev-center objective exactly
when it belongs to the closed convex hull of its active farthest-point set. -/
theorem mem_argmin_chebyshevCenterObjective_iff_mem_closedConvexHull_activeSet
    (hC_nonempty : C.Nonempty) (hCcompact : IsCompact C) (r : H) :
    r ∈ Argmin (chebyshevCenterObjective C hC_nonempty).asEReal ↔
      r ∈ closedConvexHull ℝ (Φ[C] r) := sorry

end InnerProduct

section Complete

variable [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: boundedness makes the objective everywhere finite, and as a supremum of
-- continuous squared-distance functions it is lower semicontinuous; combine this with the strong
-- convexity from clause (2) and Corollary 11.17 to get a unique global minimizer.
/-- Proposition 17.25 (9): clause (v). For a nonempty bounded set, the Chebyshev-center objective
has a unique global minimizer. -/
theorem existsUnique_mem_argmin_chebyshevCenterObjective
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    ∃! r : H, r ∈ Argmin (chebyshevCenterObjective C hC_nonempty).asEReal := sorry

end Complete
