/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_5
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

-- Semantic recall: `Matrix.PosSemidef` and `Matrix.PosDef` give the canonical matrix-positivity
-- API, while Chapter 8 already owns both the standard constrained optimization presentation and
-- the convex-programming owner used here. This file therefore keeps the source-facing
-- matrix-based quadratic-program owner and bridges it to the Chapter 8/Chapter 1 APIs instead of
-- re-declaring that public surface.

section

variable {n me mi : ℕ}

/-- The matrix-based quadratic-program owner used for Chapter09 Definition 9.1-extra-1 (1) is
determined by a
symmetric matrix `G`, a linear term `g`, equality constraints `Aeq x = beq`, and inequality
constraints `Aineq x ≥ bineq`. The finite index sets `E = {1, ..., me}` and
`I = {me + 1, ..., me + mi}` are encoded by the row types `Fin me` and `Fin mi`. -/
structure QuadraticProgram (n me mi : ℕ) where
  G : Matrix (Fin n) (Fin n) ℝ
  hG_symm : G.IsSymm
  g : EuclideanSpace ℝ (Fin n)
  Aeq : Matrix (Fin me) (Fin n) ℝ
  beq : EuclideanSpace ℝ (Fin me)
  Aineq : Matrix (Fin mi) (Fin n) ℝ
  bineq : EuclideanSpace ℝ (Fin mi)

namespace QuadraticProgram

/-- The quadratic objective of a quadratic program is `Q(x) = (1 / 2) xᵀ G x + gᵀ x`. -/
abbrev objective (P : QuadraticProgram n me mi) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct P.g x

/-- Expanding `objective` gives the source formula
`Q(x) = (1 / 2) xᵀ G x + gᵀ x`. -/
theorem objective_eq (P : QuadraticProgram n me mi) (x : EuclideanSpace ℝ (Fin n)) :
    P.objective x = (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct P.g x :=
  rfl

/-- The feasible set of a quadratic program consists of the points satisfying the linear
equality constraints and the linear inequality constraints. -/
def feasibleSet (P : QuadraticProgram n me mi) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | P.Aeq.mulVec x = P.beq ∧ ∀ i : Fin mi, P.bineq i ≤ (P.Aineq.mulVec x) i}

/-- Feasibility in a quadratic program is membership in its feasible set. -/
@[simp] theorem mem_iff (P : QuadraticProgram n me mi) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ P.feasibleSet ↔
      P.Aeq.mulVec x = P.beq ∧ ∀ i : Fin mi, P.bineq i ≤ (P.Aineq.mulVec x) i :=
  Iff.rfl

/-- Membership in `feasibleSet` is exactly the conjunction of the equality and inequality
constraints. -/
theorem mem_feasibleSet_iff (P : QuadraticProgram n me mi) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ P.feasibleSet ↔
      P.Aeq.mulVec x = P.beq ∧ ∀ i : Fin mi, P.bineq i ≤ (P.Aineq.mulVec x) i :=
  Iff.rfl

/-- The combined Chapter 8 constraint family associated to a quadratic program uses the first
`me` indices for equality constraints and the remaining `mi` indices for inequality constraints. -/
def standardConstraint (P : QuadraticProgram n me mi) (i : Fin (me + mi))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  match finSumFinEquiv.symm i with
  | Sum.inl j => (P.Aeq.mulVec x) j - P.beq j
  | Sum.inr j => (P.Aineq.mulVec x) j - P.bineq j

/-- On the equality side, `standardConstraint` is the residual `aᵢᵀ x - bᵢ`. -/
theorem standardConstraint_castAdd_eq (P : QuadraticProgram n me mi) (i : Fin me)
    (x : EuclideanSpace ℝ (Fin n)) :
    P.standardConstraint (Fin.castAdd mi i) x = (P.Aeq.mulVec x) i - P.beq i := by
  simp [QuadraticProgram.standardConstraint]

/-- On the inequality side, `standardConstraint` is the residual `aᵢᵀ x - bᵢ`, so the
Chapter 8 constraint convention `0 ≤ cᵢ(x)` matches the source inequality
`aᵢᵀ x ≥ bᵢ`. -/
theorem standardConstraint_natAdd_eq (P : QuadraticProgram n me mi) (i : Fin mi)
    (x : EuclideanSpace ℝ (Fin n)) :
    P.standardConstraint (Fin.natAdd me i) x = (P.Aineq.mulVec x) i - P.bineq i := by
  simp [QuadraticProgram.standardConstraint]

/-- Forgetting the matrix presentation produces the Chapter 8 standard constrained optimization
problem with contiguous equality and inequality blocks. -/
def toStandardConstrainedOptimizationProblem
    (P : QuadraticProgram n me mi) :
    StandardConstrainedOptimizationProblem n (me + mi) where
  eqCount := me
  eqCount_le := Nat.le_add_right me mi
  objective := fun x ↦ P.objective ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
  constraint := fun i x ↦ P.standardConstraint i ((EuclideanSpace.equiv (Fin n) ℝ).symm x)

/-- Pulling the Chapter 8 feasible set back along the Euclidean-space coordinate equivalence
recovers the original matrix-based feasible set. -/
theorem toStandardConstrainedOptimizationProblem_feasibleSet
    (P : QuadraticProgram n me mi) :
      (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹'
          P.toStandardConstrainedOptimizationProblem.feasibleSet =
        P.feasibleSet := by
  ext x
  constructor
  · intro hx
    rcases
        (P.toStandardConstrainedOptimizationProblem.mem_feasibleSet_iff
          ((EuclideanSpace.equiv (Fin n) ℝ) x)).1 hx with
      ⟨heq, hineq⟩
    refine ⟨?_, ?_⟩
    · ext i
      -- The equality block of the Chapter 8 owner recovers the original equalities.
      have hiMem : Fin.castAdd mi i ∈ P.toStandardConstrainedOptimizationProblem.eqIndices := by
        simp [StandardConstrainedOptimizationProblem.eqIndices,
          QuadraticProgram.toStandardConstrainedOptimizationProblem]
      have hi := heq (Fin.castAdd mi i) hiMem
      have hi' : P.Aeq.mulVec x.ofLp i = P.beq i := by
        change P.Aeq.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x) i = P.beq i
        simpa [QuadraticProgram.toStandardConstrainedOptimizationProblem,
          QuadraticProgram.standardConstraint_castAdd_eq, sub_eq_zero] using hi
      exact hi'
    · intro i
      -- The inequality block of the Chapter 8 owner recovers the original inequalities.
      have hiMem :
          Fin.natAdd me i ∈ P.toStandardConstrainedOptimizationProblem.ineqIndices := by
        simp [StandardConstrainedOptimizationProblem.ineqIndices,
          QuadraticProgram.toStandardConstrainedOptimizationProblem]
      have hi := hineq (Fin.natAdd me i) hiMem
      have hi' : P.bineq i ≤ P.Aineq.mulVec x.ofLp i := by
        change P.bineq i ≤ P.Aineq.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x) i
        simpa [QuadraticProgram.toStandardConstrainedOptimizationProblem,
          QuadraticProgram.standardConstraint_natAdd_eq, sub_nonneg] using hi
      exact hi'
  · rintro ⟨hEq, hIneq⟩
    refine
      (P.toStandardConstrainedOptimizationProblem.mem_feasibleSet_iff
        ((EuclideanSpace.equiv (Fin n) ℝ) x)).2 ?_
    constructor
    · intro i hi
      rcases h : finSumFinEquiv.symm i with j | j
      · have hi' : i = Fin.castAdd mi j := by
          simpa using congrArg finSumFinEquiv h
        subst hi'
        -- Equality constraints come directly from the matrix equation `Aeq x = beq`.
        have hEqj : P.Aeq.mulVec x.ofLp j = P.beq j := congrArg (fun v ↦ v j) hEq
        have hEqj' : P.Aeq.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x) j = P.beq j := by
          change P.Aeq.mulVec x.ofLp j = P.beq j
          exact hEqj
        simpa [QuadraticProgram.toStandardConstrainedOptimizationProblem,
          QuadraticProgram.standardConstraint_castAdd_eq, sub_eq_zero] using hEqj'
      · have hi' : i = Fin.natAdd me j := by
          simpa using congrArg finSumFinEquiv h
        subst hi'
        exfalso
        simp [StandardConstrainedOptimizationProblem.eqIndices,
          QuadraticProgram.toStandardConstrainedOptimizationProblem] at hi
    · intro i hi
      rcases h : finSumFinEquiv.symm i with j | j
      · have hi' : i = Fin.castAdd mi j := by
          simpa using congrArg finSumFinEquiv h
        subst hi'
        exfalso
        have hij : me ≤ j := by
          simpa [StandardConstrainedOptimizationProblem.ineqIndices,
            QuadraticProgram.toStandardConstrainedOptimizationProblem] using hi
        exact Nat.not_le_of_lt j.isLt hij
      · have hi' : i = Fin.natAdd me j := by
          simpa using congrArg finSumFinEquiv h
        subst hi'
        -- Inequality constraints come directly from `Aineq x ≥ bineq`.
        have hIneq' : P.bineq j ≤ P.Aineq.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x) j := by
          change P.bineq j ≤ P.Aineq.mulVec x.ofLp j
          exact hIneq j
        simpa [QuadraticProgram.toStandardConstrainedOptimizationProblem,
          QuadraticProgram.standardConstraint_natAdd_eq, sub_nonneg] using hIneq'

/-- Forgetting further to the Chapter 1 owner reuses the canonical Chapter 8 bridge. -/
abbrev toConstrainedOptimizationProblem (P : QuadraticProgram n me mi) :
    ConstrainedOptimizationProblem n (me + mi)
      P.toStandardConstrainedOptimizationProblem.eqIndices
      P.toStandardConstrainedOptimizationProblem.ineqIndices :=
  P.toStandardConstrainedOptimizationProblem.toConstrainedOptimizationProblem

/-- A Euclidean-space point is feasible for the Chapter 1 bridge exactly when it is feasible for
the original quadratic program. -/
theorem mem_toConstrainedOptimizationProblem_iff
    (P : QuadraticProgram n me mi) (x : EuclideanSpace ℝ (Fin n)) :
      (EuclideanSpace.equiv (Fin n) ℝ) x ∈ P.toConstrainedOptimizationProblem ↔
      x ∈ P.feasibleSet := by
  change
        x ∈ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹'
            P.toStandardConstrainedOptimizationProblem.feasibleSet ↔
        x ∈ P.feasibleSet
  rw [QuadraticProgram.toStandardConstrainedOptimizationProblem_feasibleSet]

/-- Helper for Chapter09 Definition 9.1-extra-1: an affine scalar map is concave on `Set.univ`.
-/
lemma affineMapConcaveOnUniv {n : ℕ} (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) :
    ConcaveOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Rewrite the affine combination through `lineMap`, where affine maps preserve the segment.
  refine le_of_eq ?_
  have ha' : a = 1 - b := by
    linarith
  calc
    a * f x + b * f y = AffineMap.lineMap (f x) (f y) b := by
      simp [AffineMap.lineMap_apply_module, ha']
    _ = f (AffineMap.lineMap x y b) := by
      rw [← f.apply_lineMap]
    _ = f (a • x + b • y) := by
      simp [AffineMap.lineMap_apply_module, ha']

/-- Helper for Chapter09 Definition 9.1-extra-1: the transported objective on `Fin n → ℝ` keeps
the textbook quadratic form with linear term `P.g`. -/
lemma objectiveTransport_eq (P : QuadraticProgram n me mi) (x : Fin n → ℝ) :
    P.toStandardConstrainedOptimizationProblem.objective x =
      (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct P.g.ofLp x :=
  rfl

/-- Helper for Chapter09 Definition 9.1-extra-1: each transported constraint of the Chapter 8
standard problem is an affine scalar map. -/
lemma standardConstraint_affine (P : QuadraticProgram n me mi) (i : Fin (me + mi)) :
    ∃ c : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      P.toStandardConstrainedOptimizationProblem.constraint i = c := by
  rcases h : finSumFinEquiv.symm i with j | j
  · refine
      ⟨((LinearMap.proj j).comp P.Aeq.mulVecLin).toAffineMap +
          AffineMap.const ℝ (Fin n → ℝ) (-P.beq j), ?_⟩
    have hi : i = Fin.castAdd mi j := by
      simpa using congrArg finSumFinEquiv h
    subst hi
    -- The equality block is one matrix row followed by subtraction of the right-hand side.
    ext x
    change
      P.standardConstraint (Fin.castAdd mi j) ((EuclideanSpace.equiv (Fin n) ℝ).symm x) =
        (((LinearMap.proj j).comp P.Aeq.mulVecLin).toAffineMap +
          AffineMap.const ℝ (Fin n → ℝ) (-P.beq j)) x
    simp [QuadraticProgram.standardConstraint_castAdd_eq, sub_eq_add_neg]
  · refine
      ⟨((LinearMap.proj j).comp P.Aineq.mulVecLin).toAffineMap +
          AffineMap.const ℝ (Fin n → ℝ) (-P.bineq j), ?_⟩
    have hi : i = Fin.natAdd me j := by
      simpa using congrArg finSumFinEquiv h
    subst hi
    -- The inequality block has the same affine form with the inequality data.
    ext x
    change
      P.standardConstraint (Fin.natAdd me j) ((EuclideanSpace.equiv (Fin n) ℝ).symm x) =
        (((LinearMap.proj j).comp P.Aineq.mulVecLin).toAffineMap +
          AffineMap.const ℝ (Fin n → ℝ) (-P.bineq j)) x
    simp [QuadraticProgram.standardConstraint_natAdd_eq, sub_eq_add_neg]

/-- Helper for Chapter09 Definition 9.1-extra-1: every transported constraint of the Chapter 1
bridge is concave on `Set.univ` because it is affine. -/
lemma standardConstraint_concave (P : QuadraticProgram n me mi) (i : Fin (me + mi)) :
    ConcaveOn ℝ Set.univ (P.toConstrainedOptimizationProblem.constraint i) := by
  rcases P.standardConstraint_affine i with ⟨c, hc⟩
  -- Transport the affine witness from the Chapter 8 owner to the Chapter 1 owner.
  have hc' : P.toConstrainedOptimizationProblem.constraint i = c := by
    change P.toStandardConstrainedOptimizationProblem.constraint i = c
    exact hc
  simpa [hc'] using
    affineMapConcaveOnUniv c

/-- Helper for Chapter09 Definition 9.1-extra-1: the quadratic objective satisfies the standard
weighted expansion with remainder governed by `dotProduct (x - y) (P.G.mulVec (x - y))`. -/
lemma objective_combo_sub_eq
    (P : QuadraticProgram n me mi) (a b : ℝ) (hab : a + b = 1)
    (x y : EuclideanSpace ℝ (Fin n)) :
    P.objective (a • x + b • y) =
      a * P.objective x + b * P.objective y -
        (a * b / 2) * dotProduct (x - y) (P.G.mulVec (x - y)) := by
  have hxy : dotProduct x (P.G.mulVec y) = dotProduct y (P.G.mulVec x) := by
    simpa [P.hG_symm.eq] using
      Matrix.dotProduct_transpose_mulVec (A := P.G) (x := x) (y := y)
  have hb : b = 1 - a := by
    linarith
  subst hb
  -- Expand the quadratic expression and collapse the symmetric cross terms.
  simp [QuadraticProgram.objective, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, dotProduct_neg,
    sub_eq_add_neg, hxy]
  ring_nf

/-- Helper for Chapter09 Definition 9.1-extra-1: convexity of the quadratic objective forces the
matrix `G` to be positive semidefinite. -/
lemma posSemidef_of_convexOnObjective
    (P : QuadraticProgram n me mi) (hconv : ConvexOn ℝ Set.univ P.objective) :
    P.G.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.isHermitian_iff_isSymm] using P.hG_symm
  · intro x
    let u : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm x
    -- Evaluate convexity at the segment from `u` to `0`; the remainder is exactly the quadratic
    -- form of `x`.
    have hconv2 := hconv.2
    have hmid := hconv2 (x := u) (by simp : u ∈ Set.univ) (y := 0)
      (by simp : (0 : EuclideanSpace ℝ (Fin n)) ∈ Set.univ)
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [P.objective_combo_sub_eq (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) u 0] at hmid
    simp [u, QuadraticProgram.objective] at hmid
    simpa using hmid

/-- The associated Chapter 8 standard constrained problem is quadratic programming. -/
theorem toStandardConstrainedOptimizationProblem_isQuadraticProgramming
    (P : QuadraticProgram n me mi) :
    P.toStandardConstrainedOptimizationProblem.IsQuadraticProgramming := by
  refine ⟨?_, ?_⟩
  · -- Each transported constraint is affine by construction from a matrix row plus a constant.
    intro i
    exact P.standardConstraint_affine i
  · -- The transported objective is the same quadratic form with zero constant term.
    refine ⟨P.G, P.g.ofLp, 0, ?_⟩
    ext x
    simp [P.objectiveTransport_eq]

/-- The feasible set of a quadratic program is convex because its constraints are linear. -/
theorem convex_feasibleSet (P : QuadraticProgram n me mi) :
    Convex ℝ P.feasibleSet := by
  have hBridge :
      Convex ℝ P.toConstrainedOptimizationProblem.feasibleSet := by
    -- The Chapter 1 bridge sees affine equality constraints and concave inequality constraints.
    refine ConstrainedOptimizationProblem.convex_feasibleSet_of_eq_affine_of_ineq_concave
      P.toConstrainedOptimizationProblem ?_ ?_
    · intro i hi
      change ∃ c : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
        P.toStandardConstrainedOptimizationProblem.constraint i = c
      exact P.standardConstraint_affine i
    · intro i hi
      simpa [QuadraticProgram.toConstrainedOptimizationProblem] using
        P.standardConstraint_concave i
  have hPullback :
      Convex ℝ
        ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' P.toConstrainedOptimizationProblem.feasibleSet) := by
    -- Pull convexity back through the coordinate equivalence.
    simpa using hBridge.affine_preimage ((EuclideanSpace.equiv (Fin n) ℝ).toAffineMap)
  simpa [QuadraticProgram.toConstrainedOptimizationProblem,
    QuadraticProgram.toStandardConstrainedOptimizationProblem_feasibleSet] using hPullback

/-- If `G` is positive semidefinite, then the quadratic objective is convex. Together with
`convex_feasibleSet`, this is the convex-QP clause of the source definition. -/
theorem convexOn_objective_of_posSemidef
    (P : QuadraticProgram n me mi) (hG : P.G.PosSemidef) :
    ConvexOn ℝ Set.univ P.objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- The quadratic remainder is nonnegative under positive semidefiniteness.
  rw [P.objective_combo_sub_eq a b hab x y]
  refine sub_le_self _ ?_
  refine mul_nonneg ?_ (hG.dotProduct_mulVec_nonneg (x - y))
  exact div_nonneg (mul_nonneg ha hb) (by norm_num)

/-- Chapter09 Definition 9.1-extra-1: if `G` is positive semidefinite, then the Chapter 1
bridge of `P` is a convex programming problem in the canonical Chapter 8 sense. This packages
the source convex-QP clause into the repository owner
`ConstrainedOptimizationProblem.IsConvexProgramming`. -/
theorem toConstrainedOptimizationProblem_isConvexProgramming_of_posSemidef
    (P : QuadraticProgram n me mi) (hG : P.G.PosSemidef) :
    P.toConstrainedOptimizationProblem.IsConvexProgramming := by
  refine ConstrainedOptimizationProblem.isConvexProgramming_of_convexOn_of_eq_affine_of_ineq_concave
    P.toConstrainedOptimizationProblem ?_ ?_ ?_
  · -- Transport convexity of the Euclidean-space objective to the `Fin n → ℝ` presentation.
    change ConvexOn ℝ Set.univ (P.objective ∘ ⇑(EuclideanSpace.equiv (Fin n) ℝ).symm)
    simpa using
      (P.convexOn_objective_of_posSemidef hG).comp_affineMap
        ((EuclideanSpace.equiv (Fin n) ℝ).symm.toAffineMap)
  · intro i hi
    change ∃ c : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      P.toStandardConstrainedOptimizationProblem.constraint i = c
    exact P.standardConstraint_affine i
  · intro i hi
    simpa [QuadraticProgram.toConstrainedOptimizationProblem] using
      P.standardConstraint_concave i

/-- If `G` is positive semidefinite, then every feasible local solution `xStar` of the quadratic
program is a global solution. -/
theorem isMinOn_of_isLocalMinOn_of_posSemidef
    (P : QuadraticProgram n me mi) (hG : P.G.PosSemidef)
    {xStar : EuclideanSpace ℝ (Fin n)}
    (hxStar_mem : xStar ∈ P.feasibleSet)
    (hxStar : IsLocalMinOn P.objective P.feasibleSet xStar) :
    IsMinOn P.objective P.feasibleSet xStar := by
  -- Restrict convexity from `Set.univ` to the convex feasible set.
  exact IsMinOn.of_isLocalMinOn_of_convexOn hxStar_mem hxStar <|
    (P.convexOn_objective_of_posSemidef hG).subset (by simp) P.convex_feasibleSet

/-- If `G` is positive definite, then the quadratic objective is strictly convex. This is the
strict-convex-QP clause of the source definition. -/
theorem strictConvexOn_objective_of_posDef
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef) :
    StrictConvexOn ℝ Set.univ P.objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  -- Positive definiteness makes the quadratic remainder strictly positive away from the diagonal.
  rw [P.objective_combo_sub_eq a b hab x y]
  refine sub_lt_self _ ?_
  have hsub :
      (((x - y : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) ≠ 0) := by
    intro h0
    apply hxy
    ext i
    have hi : x.ofLp i + -y.ofLp i = 0 := by
      simpa [sub_eq_add_neg] using congrFun h0 i
    linarith
  refine mul_pos (div_pos (mul_pos ha hb) (by norm_num)) ?_
  simpa using
    hG.dotProduct_mulVec_pos
      (x := ((x - y : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)) hsub

/-- If `G` is positive definite, then every feasible local solution `xStar` of the quadratic
program is a global solution. -/
theorem isMinOn_of_isLocalMinOn_of_posDef
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef)
    {xStar : EuclideanSpace ℝ (Fin n)}
    (hxStar_mem : xStar ∈ P.feasibleSet)
    (hxStar : IsLocalMinOn P.objective P.feasibleSet xStar) :
    IsMinOn P.objective P.feasibleSet xStar := by
  -- Positive definite matrices are positive semidefinite, so the convex local-to-global result
  -- applies immediately.
  exact P.isMinOn_of_isLocalMinOn_of_posSemidef hG.posSemidef hxStar_mem hxStar

/-- If `G` is positive definite, then a feasible global solution of the quadratic program is
unique. -/
theorem eq_of_isMinOn_of_posDef
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef)
    {xStar yStar : EuclideanSpace ℝ (Fin n)}
    (hxStar_mem : xStar ∈ P.feasibleSet)
    (hxStar : IsMinOn P.objective P.feasibleSet xStar)
    (hyStar_mem : yStar ∈ P.feasibleSet)
    (hyStar : IsMinOn P.objective P.feasibleSet yStar) :
    xStar = yStar := by
  have hStrict :
      StrictConvexOn ℝ P.feasibleSet P.objective := by
    -- Restrict strict convexity from the whole space to the feasible set.
    exact
      (P.strictConvexOn_objective_of_posDef hG).subset (by simp) P.convex_feasibleSet
  exact hStrict.eq_of_isMinOn hxStar hyStar hxStar_mem hyStar_mem

/-- If `G` is indefinite, written explicitly as neither `G` nor `-G` positive semidefinite,
then the quadratic objective is not convex. This is the source nonconvex-QP clause. -/
theorem not_convexOn_objective_of_indefinite
    (P : QuadraticProgram n me mi)
    (h_not_posSemidef : ¬ P.G.PosSemidef)
    (_h_not_negSemidef : ¬ (-P.G).PosSemidef) :
    ¬ ConvexOn ℝ Set.univ P.objective := by
  -- Route correction: the contradiction only needs `¬ P.G.PosSemidef`; the negated
  -- semidefiniteness of `-P.G` is redundant for this direction.
  intro hconv
  exact h_not_posSemidef (P.posSemidef_of_convexOnObjective hconv)

end QuadraticProgram

end
