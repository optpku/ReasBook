/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace ADMM

/-- The fixed data of a finite-dimensional two-block ADMM problem. -/
structure Problem (n₁ n₂ m : ℕ) where
  /-- The first extended-real objective. -/
  f : (Fin n₁ → ℝ) → EReal
  /-- The second extended-real objective. -/
  g : (Fin n₂ → ℝ) → EReal
  /-- The matrix multiplying the first primal block. -/
  A : Matrix (Fin m) (Fin n₁) ℝ
  /-- The matrix multiplying the second primal block. -/
  B : Matrix (Fin m) (Fin n₂) ℝ
  /-- The right-hand side of the equality constraint. -/
  b : Fin m → ℝ

namespace Problem

/-- Construct a two-block ADMM problem from its objective and constraint data. -/
def ofData {n₁ n₂ m : ℕ} (f : (Fin n₁ → ℝ) → EReal)
    (g : (Fin n₂ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Fin m → ℝ) : Problem n₁ n₂ m :=
  ⟨f, g, A, B, b⟩

/-- The first objective of `Problem.ofData` is the supplied first objective. -/
lemma ofData_f {n₁ n₂ m : ℕ} (f : (Fin n₁ → ℝ) → EReal)
    (g : (Fin n₂ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Fin m → ℝ) :
    (ofData f g A B b).f = f := by
  -- Reduce the constructor projection to the supplied first objective.
  rfl

/-- The second objective of `Problem.ofData` is the supplied second objective. -/
lemma ofData_g {n₁ n₂ m : ℕ} (f : (Fin n₁ → ℝ) → EReal)
    (g : (Fin n₂ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Fin m → ℝ) :
    (ofData f g A B b).g = g := by
  -- Reduce the constructor projection to the supplied second objective.
  rfl

/-- The first constraint matrix of `Problem.ofData` is the supplied matrix. -/
lemma ofData_A {n₁ n₂ m : ℕ} (f : (Fin n₁ → ℝ) → EReal)
    (g : (Fin n₂ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Fin m → ℝ) :
    (ofData f g A B b).A = A := by
  -- Reduce the constructor projection to the supplied first matrix.
  rfl

/-- The second constraint matrix of `Problem.ofData` is the supplied matrix. -/
lemma ofData_B {n₁ n₂ m : ℕ} (f : (Fin n₁ → ℝ) → EReal)
    (g : (Fin n₂ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Fin m → ℝ) :
    (ofData f g A B b).B = B := by
  -- Reduce the constructor projection to the supplied second matrix.
  rfl

/-- The constraint right-hand side of `Problem.ofData` is the supplied vector. -/
lemma ofData_b {n₁ n₂ m : ℕ} (f : (Fin n₁ → ℝ) → EReal)
    (g : (Fin n₂ → ℝ) → EReal) (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (b : Fin m → ℝ) :
    (ofData f g A B b).b = b := by
  -- Reduce the constructor projection to the supplied right-hand side.
  rfl

/-- The unconstrained sum of the two objectives at a primal pair. -/
noncomputable def objective {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : EReal :=
  P.f x + P.g y

/-- Evaluation of the objective of a two-block problem. -/
lemma objective_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    P.objective x y = P.f x + P.g y := by
  -- Unfolding the objective exposes the sum of its two blocks.
  rfl

/-- Both objectives have closed convex finite epigraphs, never take `⊥`, and are
finite at some point. -/
def IsClosedProperConvex {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) : Prop :=
  (Convex ℝ {z : (Fin n₁ → ℝ) × ℝ | P.f z.1 ≤ (z.2 : EReal)} ∧
    IsClosed {z : (Fin n₁ → ℝ) × ℝ | P.f z.1 ≤ (z.2 : EReal)} ∧
    (∀ x, P.f x ≠ ⊥) ∧ Set.Nonempty {x | P.f x ≠ ⊤}) ∧
  (Convex ℝ {z : (Fin n₂ → ℝ) × ℝ | P.g z.1 ≤ (z.2 : EReal)} ∧
    IsClosed {z : (Fin n₂ → ℝ) × ℝ | P.g z.1 ≤ (z.2 : EReal)} ∧
    (∀ y, P.g y ≠ ⊥) ∧ Set.Nonempty {y | P.g y ≠ ⊤})

/-- Characterization of closed proper convexity for both objectives of a problem. -/
lemma isClosedProperConvex_iff {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) :
    P.IsClosedProperConvex ↔
      (Convex ℝ {z : (Fin n₁ → ℝ) × ℝ | P.f z.1 ≤ (z.2 : EReal)} ∧
        IsClosed {z : (Fin n₁ → ℝ) × ℝ | P.f z.1 ≤ (z.2 : EReal)} ∧
        (∀ x, P.f x ≠ ⊥) ∧ Set.Nonempty {x | P.f x ≠ ⊤}) ∧
      (Convex ℝ {z : (Fin n₂ → ℝ) × ℝ | P.g z.1 ≤ (z.2 : EReal)} ∧
        IsClosed {z : (Fin n₂ → ℝ) × ℝ | P.g z.1 ≤ (z.2 : EReal)} ∧
        (∀ y, P.g y ≠ ⊥) ∧ Set.Nonempty {y | P.g y ≠ ⊤}) := by
  -- Unfolding the predicate exposes exactly the two displayed objective conditions.
  rfl

/-- A primal pair is feasible when it satisfies the linear equality constraint. -/
def IsFeasible {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : Prop :=
  P.A.mulVec x + P.B.mulVec y = P.b

/-- Feasibility is exactly satisfaction of the linear equality constraint. -/
lemma isFeasible_iff {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    P.IsFeasible x y ↔ P.A.mulVec x + P.B.mulVec y = P.b := by
  -- Unfolding feasibility exposes precisely the displayed constraint equation.
  rfl

end Problem

/-- `p` is a subgradient of an extended-real objective `f` at the finite point `x`. -/
def IsSubgradientAt {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (p x : Fin n → ℝ) : Prop :=
  ∃ c : ℝ, f x = c ∧ ∀ z, f x + dotProduct p (z - x) ≤ f z

/-- Supporting-plane characterization of an extended-real subgradient at a finite point. -/
lemma isSubgradientAt_iff {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (p x : Fin n → ℝ) :
    IsSubgradientAt f p x ↔
      ∃ c : ℝ, f x = c ∧ ∀ z, f x + dotProduct p (z - x) ≤ f z := by
  -- The displayed supporting-plane condition is the defining predicate.
  rfl

/-- `x` is a global minimizer of `φ` and the attained value is finite. -/
def IsFiniteMinimizer {n : ℕ} (φ : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Prop :=
  ∃ c : ℝ, φ x = c ∧ ∀ z, φ x ≤ φ z

/-- Characterization of a finite attained global minimum. -/
lemma isFiniteMinimizer_iff {n : ℕ} (φ : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    IsFiniteMinimizer φ x ↔ ∃ c : ℝ, φ x = c ∧ ∀ z, φ x ≤ φ z := by
  -- The displayed finite-minimum condition is the defining predicate.
  rfl

namespace Problem

/-- The KKT conditions are negative-transpose stationarity for both primal blocks together
with satisfaction of the equality constraint. -/
structure IsKKT {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (multiplier : Fin m → ℝ) : Prop where
  /-- Stationarity of the first primal block. -/
  firstStationary : IsSubgradientAt P.f (-P.A.transpose.mulVec multiplier) x
  /-- Stationarity of the second primal block. -/
  secondStationary : IsSubgradientAt P.g (-P.B.transpose.mulVec multiplier) y
  /-- Satisfaction of the equality constraint. -/
  feasible : P.A.mulVec x + P.B.mulVec y = P.b

namespace IsKKT

/-- Construct a KKT witness from the two stationarity conditions and primal feasibility. -/
def ofConditions {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m}
    {x : Fin n₁ → ℝ} {y : Fin n₂ → ℝ} {multiplier : Fin m → ℝ}
    (hx : IsSubgradientAt P.f (-P.A.transpose.mulVec multiplier) x)
    (hy : IsSubgradientAt P.g (-P.B.transpose.mulVec multiplier) y)
    (hfeas : P.A.mulVec x + P.B.mulVec y = P.b) : P.IsKKT x y multiplier :=
  ⟨hx, hy, hfeas⟩

end IsKKT

/-- The three KKT clauses expressed without exposing the structure constructor. -/
lemma isKKT_iff {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (multiplier : Fin m → ℝ) :
    P.IsKKT x y multiplier ↔
      IsSubgradientAt P.f (-P.A.transpose.mulVec multiplier) x ∧
      IsSubgradientAt P.g (-P.B.transpose.mulVec multiplier) y ∧
      P.A.mulVec x + P.B.mulVec y = P.b := by
  constructor
  · intro h
    -- Read the stationarity and feasibility clauses from the KKT witness.
    exact ⟨h.firstStationary, h.secondStationary, h.feasible⟩
  · rintro ⟨hx, hy, hfeas⟩
    -- Reassemble the three clauses through the public KKT constructor.
    exact IsKKT.ofConditions hx hy hfeas

/-- The set of KKT primal-dual triples of a two-block problem. -/
def kktSet {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) :
    Set ((Fin n₁ → ℝ) × (Fin n₂ → ℝ) × (Fin m → ℝ)) :=
  {q | P.IsKKT q.1 q.2.1 q.2.2}

/-- Membership in the KKT set is exactly satisfaction of the KKT conditions. -/
lemma mem_kktSet {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (q : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) × (Fin m → ℝ)) :
    q ∈ P.kktSet ↔ P.IsKKT q.1 q.2.1 q.2.2 := by
  -- Membership reduces to the predicate defining the KKT set.
  rfl

/-- The infimum of the objective over all feasible primal pairs. -/
noncomputable def optimalValue {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) : EReal :=
  sInf {q | ∃ x y, P.A.mulVec x + P.B.mulVec y = P.b ∧ q = P.objective x y}

/-- The optimal value is bounded above by every feasible objective value. -/
lemma optimalValue_le {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (hxy : P.A.mulVec x + P.B.mulVec y = P.b) :
    P.optimalValue ≤ P.objective x y := by
  unfold optimalValue
  -- Package the feasible pair as a member of the set whose infimum is taken.
  refine sInf_le ?_
  exact ⟨x, y, hxy, rfl⟩

/-- The first-block augmented objective with the second block and multiplier fixed. -/
noncomputable def firstBlockObjective {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ)
    (multiplier : Fin m → ℝ) (y : Fin n₂ → ℝ) (x : Fin n₁ → ℝ) : EReal :=
  let r := P.A.mulVec x + P.B.mulVec y - P.b
  P.f x + dotProduct multiplier r + ((β / 2) * dotProduct r r : ℝ)

/-- Evaluation of the first-block augmented objective. -/
lemma firstBlockObjective_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ)
    (multiplier : Fin m → ℝ) (y : Fin n₂ → ℝ) (x : Fin n₁ → ℝ) :
    P.firstBlockObjective β multiplier y x =
      P.f x + dotProduct multiplier (P.A.mulVec x + P.B.mulVec y - P.b) +
        ((β / 2) * dotProduct (P.A.mulVec x + P.B.mulVec y - P.b)
          (P.A.mulVec x + P.B.mulVec y - P.b) : ℝ) := by
  -- Reduce the local residual binding in the first-block objective.
  rfl

/-- The second-block augmented objective with the first block and multiplier fixed. -/
noncomputable def secondBlockObjective {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ)
    (multiplier : Fin m → ℝ) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : EReal :=
  let r := P.A.mulVec x + P.B.mulVec y - P.b
  P.g y + dotProduct multiplier r + ((β / 2) * dotProduct r r : ℝ)

/-- Evaluation of the second-block augmented objective. -/
lemma secondBlockObjective_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β : ℝ)
    (multiplier : Fin m → ℝ) (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) :
    P.secondBlockObjective β multiplier x y =
      P.g y + dotProduct multiplier (P.A.mulVec x + P.B.mulVec y - P.b) +
        ((β / 2) * dotProduct (P.A.mulVec x + P.B.mulVec y - P.b)
          (P.A.mulVec x + P.B.mulVec y - P.b) : ℝ) := by
  -- Reduce the local residual binding in the second-block objective.
  rfl

/-- The relaxed multiplier obtained from a primal pair and the current multiplier. -/
def multiplierUpdate {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (multiplier : Fin m → ℝ) : Fin m → ℝ :=
  multiplier + (γ * β) • (P.A.mulVec x + P.B.mulVec y - P.b)

/-- Evaluation of the relaxed multiplier update. -/
lemma multiplierUpdate_apply {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m) (β γ : ℝ)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (multiplier : Fin m → ℝ) :
    P.multiplierUpdate β γ x y multiplier =
      multiplier + (γ * β) • (P.A.mulVec x + P.B.mulVec y - P.b) := by
  -- Unfolding the update yields the multiplier plus the scaled primal residual.
  rfl

end Problem

end ADMM
