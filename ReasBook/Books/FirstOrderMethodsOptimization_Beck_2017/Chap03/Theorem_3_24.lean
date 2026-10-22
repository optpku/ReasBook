/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)
open Matrix
open WithLp (ofLp toLp)
open scoped BigOperators

section

variable {m n p : ℕ}

local notation "PerturbationSpace" =>
  EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin p)

/- Theorem 3.24 is `source-facing` in the affine-constrained perturbation/duality API. Its
`core/canonical` owners are already the earlier chapter declarations `effective_domain`,
`IsProperExtendedRealFunction`, `is_convex_function`, the continuous-dual bridge
`strongDualSubdifferential`, and the perturbation owner `value_function` from `Lemma_3_4`. The
source theorem takes the constraint family `g₁, …, gₘ` to be extended-real-valued convex
functions, so this file keeps that owner-compatible surface directly instead of inserting a
real-valued coercion layer. -/
-- Leansearch did not surface a directly reusable owner theorem for this affine perturbation/duality
-- statement, so this item stays on the local chapter owners `value_function` and
-- `strongDualSubdifferential`.
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall strongDualSubdifferential
recall value_function_feasible_set
recall value_function

/-- The feasible set of the primal problem consists of the points of `X` satisfying the
coordinatewise inequality constraints `g x ≤ 0` and the affine equality constraint `A x + b = 0`.
-/
def primalFeasibleSet
    (X : Set (Fin n → ℝ))
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ X ∧ (∀ i : Fin m, g i x ≤ 0) ∧ A *ᵥ x + b = 0}

/-- Membership in the primal feasible set is exactly the textbook conjunction of set membership,
coordinatewise inequality feasibility, and affine equality feasibility. -/
@[simp] theorem mem_primalFeasibleSet
    (X : Set (Fin n → ℝ))
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (x : Fin n → ℝ) :
    x ∈ primalFeasibleSet X g A b ↔
      x ∈ X ∧ (∀ i : Fin m, g i x ≤ 0) ∧ A *ᵥ x + b = 0 :=
  Iff.rfl

/-- The source-facing primal feasible set is the zero-perturbation slice of the owner feasible-set
construction after transporting the primal variables into Euclidean space. -/
@[simp] theorem toLp_mem_value_function_feasible_set_zero_iff
    (X : Set (Fin n → ℝ))
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (x : Fin n → ℝ) :
    toLp 2 x ∈
        value_function_feasible_set
          (toLp 2 '' X)
          (fun i x ↦ g i (ofLp x))
          A.toEuclideanLin
          (toLp 2 b)
          0
          0 ↔
      x ∈ primalFeasibleSet X g A b := by
  constructor
  · intro hx
    have hx' : x ∈ X ∧ (∀ i : Fin m, g i x ≤ 0) ∧ toLp 2 (A *ᵥ x) + toLp 2 b = 0 := by
      simpa [Matrix.toLpLin_toLp] using hx
    rcases hx' with ⟨hxX, hxg, hEq⟩
    have : toLp 2 (A *ᵥ x + b) = 0 := by
      simpa using hEq
    exact (mem_primalFeasibleSet X g A b x).2
      ⟨hxX, hxg, by simpa using congrArg ofLp this⟩
  · intro hx
    rcases (mem_primalFeasibleSet X g A b x).1 hx with ⟨hxX, hxg, hEq⟩
    have hEq' : toLp 2 (A *ᵥ x + b) = 0 := by
      simpa using congrArg (toLp 2) hEq
    have hx' : x ∈ X ∧ (∀ i : Fin m, g i x ≤ 0) ∧ toLp 2 (A *ᵥ x) + toLp 2 b = 0 := by
      exact ⟨hxX, hxg, by simpa using hEq'⟩
    simpa [Matrix.toLpLin_toLp] using hx'

/-- The Lagrangian dual objective is the infimum over the points of `X` whose constraint vector is
finite, so the perturbation slice `(g x, A x + b)` is a genuine point of `ℝ^m × ℝ^p`. Points with
some `g i x = ⊤` are assigned the inert value `⊤`, matching the source proof step
`f x ≥ v (g x, A x + b)` and preventing non-real perturbation vectors from lowering the dual
objective through the convention `0 * ⊤ = 0` in `EReal`. -/
def lagrangianDualObjective
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (y : Fin m → ℝ) (z : Fin p → ℝ) : EReal :=
  sInf ((fun x : Fin n → ℝ ↦
    if ∀ i : Fin m, g i x ≠ ⊤ then
      f x +
        ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) +
        ∑ j : Fin p, ((z j * (A *ᵥ x + b) j : ℝ) : EReal)
    else
      ⊤) '' X)

/-- The dual objective values attained by nonnegative inequality multipliers. -/
def dualObjectiveValues
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    Set EReal :=
  {q | ∃ y : Fin m → ℝ, ∃ z : Fin p → ℝ,
      (∀ i : Fin m, 0 ≤ y i) ∧ lagrangianDualObjective X f g A b y z = q}

/-- Membership in `dualObjectiveValues X f g A b` means that the value is attained by a multiplier
pair `(y, z)` with coordinatewise nonnegative inequality component `y`. -/
@[simp] theorem mem_dualObjectiveValues
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (q : EReal) :
    q ∈ dualObjectiveValues X f g A b ↔
      ∃ y : Fin m → ℝ, ∃ z : Fin p → ℝ,
        (∀ i : Fin m, 0 ≤ y i) ∧ lagrangianDualObjective X f g A b y z = q :=
  Iff.rfl

/-- A real number is the primal optimal value when it is the greatest lower bound of the feasible
objective values. -/
def IsPrimalOptimalValue
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (fOpt : ℝ) : Prop :=
  IsGLB (f '' primalFeasibleSet X g A b) (fOpt : EReal)

/-- `IsPrimalOptimalValue X f g A b fOpt` is exactly the greatest-lower-bound condition on the
objective values attained on the primal feasible set. -/
@[simp] theorem isPrimalOptimalValue_iff
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (fOpt : ℝ) :
    IsPrimalOptimalValue X f g A b fOpt ↔
      IsGLB (f '' primalFeasibleSet X g A b) (fOpt : EReal) :=
  Iff.rfl

/-- A pair `(y, z)` is a dual optimal solution with optimal value `qOpt` when `y` is
coordinatewise nonnegative, the dual objective at `(y, z)` equals `qOpt`, and `qOpt` is the least
upper bound of all attained dual objective values. -/
def IsDualOptimalSolution
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (qOpt : ℝ) (y : Fin m → ℝ) (z : Fin p → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ y i) ∧
    lagrangianDualObjective X f g A b y z = (qOpt : EReal) ∧
    IsLUB (dualObjectiveValues X f g A b) (qOpt : EReal)

/-- `IsDualOptimalSolution X f g A b qOpt y z` expands to the nonnegativity, attainment, and
least-upper-bound conditions in the textbook definition of a dual optimal multiplier pair. -/
@[simp] theorem isDualOptimalSolution_iff
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (qOpt : ℝ) (y : Fin m → ℝ) (z : Fin p → ℝ) :
    IsDualOptimalSolution X f g A b qOpt y z ↔
      (∀ i : Fin m, 0 ≤ y i) ∧
        lagrangianDualObjective X f g A b y z = (qOpt : EReal) ∧
        IsLUB (dualObjectiveValues X f g A b) (qOpt : EReal) :=
  Iff.rfl

/-- The perturbation value function for the affine-constrained problem. This is the
`bridge/view` layer: it keeps the source-facing data `X`, `f`, `g`, `A`, and `b`, while the owner
object is the chapter declaration `value_function` on the Euclidean perturbation space
`ℝ^m × ℝ^p`. -/
abbrev valueFunction
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → EReal)
    (g : Fin m → (Fin n → ℝ) → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    PerturbationSpace → EReal :=
  value_function
    (toLp 2 '' X)
    (fun x : EuclideanSpace ℝ (Fin n) ↦ f (ofLp x))
    (fun i x ↦ g i (ofLp x))
    A.toEuclideanLin
    (toLp 2 b)

/-- The continuous-dual element corresponding to the negated multiplier pair `-(y, z)` in the
perturbation space `ℝ^m × ℝ^p`. -/
abbrev negPerturbationDualPair (y : Fin m → ℝ) (z : Fin p → ℝ) :
    StrongDual ℝ PerturbationSpace :=
  ContinuousLinearMap.coprod
    (toDualMap ℝ (EuclideanSpace ℝ (Fin m)) (toLp 2 (-y)))
    (toDualMap ℝ (EuclideanSpace ℝ (Fin p)) (toLp 2 (-z)))

section Theorem_3_24

variable
  (X : Set (Fin n → ℝ))
  (f : (Fin n → ℝ) → EReal)
  (g : Fin m → (Fin n → ℝ) → EReal)
  (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
  (fOpt : ℝ)

/-- Helper for Theorem 3.24: the zero perturbation slice of `valueFunction` recovers the primal
optimal value. -/
lemma valueFunction_zero_eq_primalOptimalValue
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt) :
    valueFunction X f g A b (0 : PerturbationSpace) = (fOpt : EReal) := by
  let primalValues : Set EReal := f '' primalFeasibleSet X g A b
  let ownerValues : Set EReal :=
    (fun x : EuclideanSpace ℝ (Fin n) ↦ f (ofLp x)) ''
      value_function_feasible_set
        (toLp 2 '' X)
        (fun i x ↦ g i (ofLp x))
        A.toEuclideanLin
        (toLp 2 b)
        0
        0
  have howner_eq_primal : ownerValues = primalValues := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' :
          toLp 2 (ofLp x) ∈
            value_function_feasible_set
              (toLp 2 '' X)
              (fun i x ↦ g i (ofLp x))
              A.toEuclideanLin
              (toLp 2 b)
              0
              0 := by
        simpa using hx
      refine ⟨ofLp x, ?_, by simp⟩
      exact (toLp_mem_value_function_feasible_set_zero_iff X g A b (ofLp x)).1 hx'
    · rintro ⟨x, hx, rfl⟩
      refine ⟨toLp 2 x, ?_, by simp⟩
      exact (toLp_mem_value_function_feasible_set_zero_iff X g A b x).2 hx
  have hprimalValues_nonempty : primalValues.Nonempty := by
    by_contra hEmpty
    have htop_lower : ∀ z ∈ primalValues, (⊤ : EReal) ≤ z := by
      intro z hz
      exact False.elim (hEmpty ⟨z, hz⟩)
    have htop_le : (⊤ : EReal) ≤ (fOpt : EReal) := hPrimal.2 htop_lower
    simp at htop_le
  -- Rewrite the owner zero slice to the primal-value set and use the GLB characterization.
  rw [valueFunction, value_function_apply]
  change sInf ownerValues = (fOpt : EReal)
  rw [howner_eq_primal]
  exact hPrimal.csInf_eq hprimalValues_nonempty

/-- Helper for Theorem 3.24: the strong-dual element `negPerturbationDualPair y z` evaluates on a
perturbation `(u, t)` as the negated multiplier pairing. -/
lemma negPerturbationDualPair_apply
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (u : EuclideanSpace ℝ (Fin m)) (t : EuclideanSpace ℝ (Fin p)) :
    ((negPerturbationDualPair y z) (u, t) : ℝ) =
      -∑ i : Fin m, y i * u i - ∑ j : Fin p, z j * t j := by
  -- Evaluate the coprod functional on each factor and normalize the real inner products to
  -- ordinary scalar multiplication.
  simp [negPerturbationDualPair, ContinuousLinearMap.coprod_apply,
    InnerProductSpace.toDualMap_apply_apply, PiLp.inner_apply, sub_eq_add_neg, mul_comm]

/-- Helper for Theorem 3.24: every point feasible for perturbation `(u, t)` satisfies the affine
lower support inequality induced by a dual-optimal multiplier pair. -/
lemma dualLowerBoundAtValueFunctionFeasiblePoint
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hDual : IsDualOptimalSolution X f g A b fOpt y z)
    {u : EuclideanSpace ℝ (Fin m)} {t : EuclideanSpace ℝ (Fin p)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈
      value_function_feasible_set
        (toLp 2 '' X)
        (fun i x ↦ g i (ofLp x))
        A.toEuclideanLin
        (toLp 2 b)
        u
        t) :
    ((fOpt : EReal) + (((negPerturbationDualPair y z) (u, t) : ℝ) : EReal))
      ≤ f (ofLp x) := by
  rcases hDual with ⟨hy, hDualValue, _hDualLub⟩
  rcases (mem_value_function_feasible_set
    (toLp 2 '' X)
    (fun i x ↦ g i (ofLp x))
    A.toEuclideanLin
    (toLp 2 b)
    u
    t
    x).1 hx with ⟨hxX, hxg, hxt⟩
  have hg_ne_top : ∀ i : Fin m, g i (ofLp x) ≠ ⊤ := by
    intro i htop
    have : (⊤ : EReal) ≤ ((u i : ℝ) : EReal) := by
      simpa [htop] using hxg i
    simp at this
  have hEq : A *ᵥ ofLp x + b = ofLp t := by
    simpa [Matrix.toLpLin_toLp] using congrArg ofLp hxt
  have hxX' : ofLp x ∈ X := by
    rcases hxX with ⟨x₀, hx₀, hx₀eq⟩
    have hxeq : ofLp x = x₀ := by
      simpa [hx₀eq] using (congrArg ofLp hx₀eq).symm
    simpa [hxeq] using hx₀
  let inequalitySum : ℝ := ∑ i : Fin m, y i * u i
  let equalitySum : ℝ := ∑ j : Fin p, z j * t j
  have coeRealSum (s : Finset (Fin m)) :
      Finset.sum s (fun i ↦ (((y i * u i : ℝ)) : EReal)) =
        (((Finset.sum s fun i ↦ y i * u i) : ℝ) : EReal) := by
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi hs
      rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, hs]
  have coeEqualitySum (s : Finset (Fin p)) :
      Finset.sum s (fun j ↦ (((z j * t j : ℝ)) : EReal)) =
        (((Finset.sum s fun j ↦ z j * t j) : ℝ) : EReal) := by
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj hs
      rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, hs]
  have hIneqTerms :
      ∑ i : Fin m, (((y i : ℝ) : EReal) * g i (ofLp x)) ≤ (inequalitySum : EReal) := by
    -- Monotonicity of the coordinate multipliers upgrades the feasible-set inequality to the
    -- multiplier-weighted inequality sum.
    have hTerm :
        ∀ i : Fin m, (((y i : ℝ) : EReal) * g i (ofLp x)) ≤ (((y i * u i : ℝ)) : EReal) := by
      intro i
      exact
        (mul_le_mul_of_nonneg_left (hxg i)
          (by exact_mod_cast hy i)).trans_eq (by simp [EReal.coe_mul])
    calc
      ∑ i : Fin m, (((y i : ℝ) : EReal) * g i (ofLp x))
          ≤ ∑ i : Fin m, (((y i * u i : ℝ)) : EReal) := Finset.sum_le_sum fun i _ ↦ hTerm i
      _ = (inequalitySum : EReal) := by
          simpa [inequalitySum] using coeRealSum Finset.univ
  have hEqTerms :
      (∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal)) = (equalitySum : EReal) := by
    -- Feasibility identifies the affine residual with the perturbation coordinate `t`.
    have hEqCoord : ∀ j : Fin p, (A *ᵥ ofLp x + b) j = t j := by
      intro j
      simpa using congrArg (fun v : Fin p → ℝ ↦ v j) hEq
    calc
      ∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal)
          = ∑ j : Fin p, ((z j * t j : ℝ) : EReal) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simp [hEqCoord j]
      _ = (equalitySum : EReal) := by
          simpa [equalitySum] using coeEqualitySum Finset.univ
  have hDualAtX :
      (fOpt : EReal) ≤
        f (ofLp x) +
          ∑ i : Fin m, (((y i : ℝ) : EReal) * g i (ofLp x)) +
          ∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal) := by
    -- Compare the dual infimum with the branch indexed by the current feasible primal point.
    rw [← hDualValue, lagrangianDualObjective]
    exact sInf_le ⟨ofLp x, hxX', by simp [hg_ne_top]⟩
  have hDualAtX' :
      (fOpt : EReal) ≤ f (ofLp x) + (inequalitySum : EReal) + (equalitySum : EReal) := by
    have hIneqStep :
        f (ofLp x) +
            ∑ i : Fin m, (((y i : ℝ) : EReal) * g i (ofLp x)) +
            ∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal)
          ≤ f (ofLp x) + (inequalitySum : EReal) +
            ∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left
          hIneqTerms
          (f (ofLp x) +
            ∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal))
    calc
      (fOpt : EReal)
          ≤ f (ofLp x) +
              ∑ i : Fin m, (((y i : ℝ) : EReal) * g i (ofLp x)) +
              ∑ j : Fin p, ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal) := hDualAtX
      _ ≤ f (ofLp x) + (inequalitySum : EReal) + ∑ j : Fin p,
            ((z j * (A *ᵥ ofLp x + b) j : ℝ) : EReal) := hIneqStep
      _ = f (ofLp x) + (inequalitySum : EReal) + (equalitySum : EReal) := by rw [hEqTerms]
  have hCancelled :
      (fOpt : EReal) - ((inequalitySum + equalitySum : ℝ) : EReal) ≤ f (ofLp x) := by
    exact EReal.sub_le_of_le_add (by
      simpa [inequalitySum, equalitySum, EReal.coe_add, add_assoc, add_left_comm, add_comm] using
        hDualAtX')
  have hNegFiniteSum :
      (-((inequalitySum : ℝ) : EReal)) + -((equalitySum : ℝ) : EReal) =
        -(((inequalitySum + equalitySum : ℝ)) : EReal) := by
    rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg]
    ring_nf
  have hCancelled' :
      (fOpt : EReal) + (((-inequalitySum - equalitySum : ℝ)) : EReal) ≤ f (ofLp x) := by
    simpa [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg, hNegFiniteSum] using hCancelled
  -- Rewrite the real subtraction back to the negated perturbation pairing.
  rw [negPerturbationDualPair_apply]
  simpa [inequalitySum, equalitySum] using hCancelled'

/-- Helper for Theorem 3.24: evaluating the negated multiplier pair on the `i`th unit inequality
perturbation picks out `-y i`. -/
lemma negPerturbationDualPair_single_apply
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (i : Fin m) :
    ((negPerturbationDualPair y z) (toLp 2 (Pi.single i 1), 0) : ℝ) = -y i := by
  -- Expand the pairing and simplify the single-coordinate perturbation.
  rw [negPerturbationDualPair_apply]
  simp [Pi.single_apply]

/-- Helper for Theorem 3.24: the self-generated perturbation slice built from `x` places `x`
itself in the feasible set, so the corresponding value function is bounded above by `f x`. -/
lemma valueFunction_le_selfPerturbationSlice
    (x : Fin n → ℝ)
    (hxX : x ∈ X)
    (hTop : ∀ i : Fin m, g i x ≠ ⊤)
    (hBot : ∀ i : Fin m, g i x ≠ ⊥) :
    valueFunction X f g A b
        (toLp 2 (fun i ↦ (g i x).toReal), toLp 2 (A *ᵥ x + b)) ≤ f x := by
  -- Use `x` itself as the witness in the owner feasible slice attached to its perturbation data.
  rw [valueFunction, value_function_apply]
  refine sInf_le ?_
  refine ⟨toLp 2 x, ?_, by simp⟩
  rw [mem_value_function_feasible_set]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨x, hxX, by simp⟩
  · intro i
    have hgi : g i x = (((g i x).toReal : ℝ) : EReal) := by
      rw [EReal.coe_toReal (hTop i) (hBot i)]
    have hle : g i (ofLp (toLp 2 x)) ≤ (((g i x).toReal : ℝ) : EReal) := by
      simpa using le_of_eq hgi
    simpa using hle
  · simp [Matrix.toLpLin_toLp]

/-- Helper for Theorem 3.24: a subgradient of `valueFunction` at the origin yields the supporting
inequality based at the primal optimal value `fOpt`. -/
lemma primalOptimalValue_add_pairing_le_valueFunction_of_mem_subdifferentialZero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hSub :
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace))) :
    ∀ perturb : PerturbationSpace,
      (fOpt : EReal) + (((negPerturbationDualPair y z perturb : ℝ) : EReal)) ≤
        valueFunction X f g A b perturb := by
  have hzero :
      valueFunction X f g A b (0 : PerturbationSpace) = (fOpt : EReal) :=
    valueFunction_zero_eq_primalOptimalValue X f g A b fOpt hPrimal
  rw [mem_strongDualSubdifferential, mem_subdifferential] at hSub
  intro perturb
  -- Rewrite the owner subgradient inequality at the origin into the source-facing support bound.
  simpa only [hzero, ge_iff_le, sub_zero] using hSub.2 perturb

/-- Helper for Theorem 3.24: a subgradient of `valueFunction` at the origin forces the inequality
multiplier `y` to be coordinatewise nonnegative. -/
lemma multiplierNonneg_of_mem_subdifferentialValueFunctionZero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hSub :
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace))) :
    ∀ i : Fin m, 0 ≤ y i := by
  have hsupport :=
    primalOptimalValue_add_pairing_le_valueFunction_of_mem_subdifferentialZero
      X f g A b fOpt y z hPrimal hSub
  have hzero :
      valueFunction X f g A b (0 : PerturbationSpace) = (fOpt : EReal) :=
    valueFunction_zero_eq_primalOptimalValue X f g A b fOpt hPrimal
  intro i
  let perturb : PerturbationSpace := (toLp 2 (Pi.single i 1), 0)
  have hslice :
      (((fOpt - y i : ℝ)) : EReal) ≤ valueFunction X f g A b perturb := by
    -- Evaluate the support inequality on the single-coordinate perturbation.
    have realInnerEqMul : ∀ a b : ℝ, inner ℝ a b = a * b := by
      intro a b
      change b * star a = a * b
      simp [mul_comm]
    simpa [perturb, PiLp.inner_apply, realInnerEqMul, sub_eq_add_neg, EReal.coe_add]
      using hsupport perturb
  have hmono :
      valueFunction X f g A b perturb ≤ valueFunction X f g A b (0 : PerturbationSpace) := by
    -- Increasing one inequality threshold from `0` to `1` can only decrease the value function.
    exact value_function_antitone_u
      (toLp 2 '' X)
      (fun x : EuclideanSpace ℝ (Fin n) ↦ f (ofLp x))
      (fun j x ↦ g j (ofLp x))
      A.toEuclideanLin
      (toLp 2 b)
      (u := 0)
      (w := toLp 2 (Pi.single i 1))
      (t := 0)
      (by
        intro j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [hji])
  have hle : (((fOpt - y i : ℝ)) : EReal) ≤ (fOpt : EReal) := by
    simpa [hzero] using hslice.trans hmono
  have hle_real : fOpt - y i ≤ fOpt := EReal.coe_le_coe_iff.mp hle
  linarith

/-- Helper for Theorem 3.24: when each constraint value `g i x` is finite, the inequality part of
the Lagrangian branch is the coercion of the corresponding real weighted sum. -/
lemma finiteConstraintWeightedSum_eq_toRealWeightedSum
    (y : Fin m → ℝ) (x : Fin n → ℝ)
    (hTop : ∀ i : Fin m, g i x ≠ ⊤)
    (hBot : ∀ i : Fin m, g i x ≠ ⊥) :
    ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) =
      ((∑ i : Fin m, y i * (g i x).toReal) : EReal) := by
  -- Normalize each finite constraint coordinate through `EReal.coe_toReal`.
  have hterm :
      ∀ i : Fin m, (((y i : ℝ) : EReal) * g i x) =
        (((y i * (g i x).toReal : ℝ)) : EReal) := by
    intro i
    rw [EReal.coe_mul, EReal.coe_toReal (hTop i) (hBot i)]
  -- Collect the pointwise normal form back into one coerced finite sum.
  have hsum :
      ∀ s : Finset (Fin m),
        Finset.sum s (fun i ↦ (((y i : ℝ) : EReal) * g i x)) =
          ((Finset.sum s fun i ↦ y i * (g i x).toReal) : EReal) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi hs
      simp [Finset.sum_insert, hi, hterm i, hs, EReal.coe_mul]
  simpa using hsum Finset.univ

/-- Helper for Theorem 3.24: the support inequality at the origin becomes the exact finite branch
of `lagrangianDualObjective` once it is specialized to the self-perturbation slice of `x`. -/
lemma primalOptimalValue_le_lagrangianFiniteBranch_of_mem_subdifferentialZero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (x : Fin n → ℝ) (hxX : x ∈ X)
    (hTop : ∀ i : Fin m, g i x ≠ ⊤)
    (hBot : ∀ i : Fin m, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hSub :
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace))) :
    (fOpt : EReal) ≤
      f x + ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) +
        ∑ j : Fin p, ((z j * (A *ᵥ x + b) j : ℝ) : EReal) := by
  let perturb : PerturbationSpace :=
    (toLp 2 (fun i ↦ (g i x).toReal), toLp 2 (A *ᵥ x + b))
  let constraintSum : ℝ := ∑ i : Fin m, y i * (g i x).toReal
  let residualSum : ℝ := ∑ j : Fin p, z j * ((A *ᵥ x) j + b j)
  have hsupport :=
    primalOptimalValue_add_pairing_le_valueFunction_of_mem_subdifferentialZero
      X f g A b fOpt y z hPrimal hSub perturb
  have hslice :
      valueFunction X f g A b perturb ≤ f x := by
    -- Use the perturbation slice generated by `x` itself.
    simpa [perturb] using valueFunction_le_selfPerturbationSlice X f g A b x hxX hTop hBot
  have hpaired :
      (fOpt : EReal) + (((negPerturbationDualPair y z perturb : ℝ) : EReal)) ≤ f x :=
    hsupport.trans hslice
  have hLower :
      (fOpt : EReal) ≤ f x - (((negPerturbationDualPair y z perturb : ℝ) : EReal)) := by
    -- Move the finite pairing term to the right-hand side before normalizing it.
    exact
      (EReal.le_sub_iff_add_le
        (Or.inl (EReal.coe_ne_bot ((negPerturbationDualPair y z perturb : ℝ))))
        (Or.inl (EReal.coe_ne_top ((negPerturbationDualPair y z perturb : ℝ))))).2
        hpaired
  have coeConstraintSum (s : Finset (Fin m)) :
      (((Finset.sum s fun i ↦ y i * (g i x).toReal : ℝ)) : EReal) =
        Finset.sum s (fun i ↦ (((y i * (g i x).toReal : ℝ)) : EReal)) := by
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi hs
      simp [Finset.sum_insert, hi, hs, EReal.coe_add]
  have hConstraintTerm :
      ∀ i : Fin m, (((y i : ℝ) : EReal) * g i x) =
        (((y i * (g i x).toReal : ℝ)) : EReal) := by
    intro i
    rw [EReal.coe_mul, EReal.coe_toReal (hTop i) (hBot i)]
  have hConstraintSum :
      (constraintSum : EReal) = ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) := by
    calc
      (constraintSum : EReal)
          = ∑ i : Fin m, (((y i * (g i x).toReal : ℝ)) : EReal) := by
              simpa [constraintSum] using coeConstraintSum Finset.univ
      _ = ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simpa using (hConstraintTerm i).symm
  have coeResidualSum (s : Finset (Fin p)) :
      (((Finset.sum s fun j ↦ z j * ((A *ᵥ x) j + b j) : ℝ)) : EReal) =
        Finset.sum s (fun j ↦ (((z j * ((A *ᵥ x) j + b j) : ℝ)) : EReal)) := by
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj hs
      simp [Finset.sum_insert, hj, hs, EReal.coe_add]
  have hResidualSum :
      (residualSum : EReal) =
        ∑ j : Fin p, ((z j * (A *ᵥ x + b) j : ℝ) : EReal) := by
    calc
      (residualSum : EReal)
          = ∑ j : Fin p, (((z j * ((A *ᵥ x) j + b j) : ℝ)) : EReal) := by
              simpa [residualSum] using coeResidualSum Finset.univ
      _ = ∑ j : Fin p, ((z j * (A *ᵥ x + b) j : ℝ) : EReal) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp
  have hNegSums :
      -(-((constraintSum : ℝ) : EReal) + -((residualSum : ℝ) : EReal)) =
        (constraintSum : EReal) + (residualSum : EReal) := by
    rw [← EReal.coe_add]
    rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg]
    congr 1
    ring_nf
  have hCoeNegSum :
      (((-constraintSum - residualSum : ℝ)) : EReal) =
        -((constraintSum : ℝ) : EReal) + -((residualSum : ℝ) : EReal) := by
    have hRealNegSum : -constraintSum - residualSum = (-constraintSum) + (-residualSum) := by
      ring_nf
    rw [hRealNegSum, EReal.coe_add, EReal.coe_neg, EReal.coe_neg]
  have hNormalize :
      f x - (((-constraintSum - residualSum : ℝ)) : EReal) =
        f x + (constraintSum : EReal) + (residualSum : EReal) := by
    -- Expand the finite real coercion once, then use the explicit negated-sum identity.
    rw [sub_eq_add_neg, hCoeNegSum, hNegSums]
    simp [add_assoc]
  -- Normalize the finite pairing and the two finite sums into the exact branch formula.
  calc
    (fOpt : EReal) ≤ f x - (((negPerturbationDualPair y z perturb : ℝ) : EReal)) := hLower
    _ =
        f x - (((-constraintSum - residualSum : ℝ)) : EReal) := by
          rw [negPerturbationDualPair_apply]
          simp [constraintSum, residualSum]
    _ =
        f x + (constraintSum : EReal) + (residualSum : EReal) := hNormalize
    _ =
        f x + ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) + (residualSum : EReal) := by
          rw [hConstraintSum]
    _ =
        f x + ∑ i : Fin m, (((y i : ℝ) : EReal) * g i x) +
          ∑ j : Fin p, ((z j * (A *ᵥ x + b) j : ℝ) : EReal) := by
          rw [hResidualSum]

/-- Theorem 3.24 auxiliary inequality: the origin subgradient inequality gives the lower bound
`fOpt ≤ lagrangianDualObjective X f g A b y z`. -/
lemma primalOptimalValue_le_lagrangianDualObjective_of_mem_subdifferentialValueFunctionZero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hSub :
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace))) :
    (fOpt : EReal) ≤ lagrangianDualObjective X f g A b y z := by
  -- Route correction: normalize each branch below the infimum, rather than rewriting the whole
  -- `sInf` expression through `PiLp.inner_apply` and `toReal` at once.
  rw [lagrangianDualObjective]
  refine le_sInf ?_
  rintro _ ⟨x, hxX, rfl⟩
  by_cases hTop : ∀ i : Fin m, g i x ≠ ⊤
  · have hBot : ∀ i : Fin m, g i x ≠ ⊥ := by
      intro i
      exact hg_ne_bot i x
    -- In the finite branch, the specialized self-perturbation slice gives the exact branch value.
    simpa [hTop] using
      primalOptimalValue_le_lagrangianFiniteBranch_of_mem_subdifferentialZero
        X f g A b fOpt y z x hxX hTop hBot hPrimal hSub
  · -- If some constraint value is `⊤`, the branch of the dual objective is definitionally `⊤`.
    simp [hTop]

/-- Helper for Theorem 3.24: a dual-optimal multiplier pair gives a strong-dual subgradient of the
perturbation value function at the origin. -/
lemma dualOptimalSolution_mem_subdifferentialValueFunctionZero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDual : IsDualOptimalSolution X f g A b fOpt y z) :
    negPerturbationDualPair y z ∈
      ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace)) := by
  have hzero :
      valueFunction X f g A b (0 : PerturbationSpace) = (fOpt : EReal) :=
    valueFunction_zero_eq_primalOptimalValue X f g A b fOpt hPrimal
  -- Rewrite strong-dual membership to the owner subgradient predicate and prove the support
  -- inequality directly on each perturbation slice.
  rw [mem_strongDualSubdifferential, mem_subdifferential]
  refine ⟨?_, ?_⟩
  · rw [mem_effective_domain, hzero]
    simp
  · rintro ⟨u, t⟩
    rw [valueFunction, value_function_apply, ge_iff_le]
    have hslice :
        (fOpt : EReal) + ((((negPerturbationDualPair y z) (u, t) : ℝ) : EReal)) ≤
          sInf
            ((fun x : EuclideanSpace ℝ (Fin n) ↦ f (ofLp x)) ''
              value_function_feasible_set
                (toLp 2 '' X)
                (fun i x ↦ g i (ofLp x))
                A.toEuclideanLin
                (toLp 2 b)
                u
                t) := by
      refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      exact dualLowerBoundAtValueFunctionFeasiblePoint X f g A b fOpt y z hDual hx
    simpa [valueFunction, hzero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hslice

/-- Helper for Theorem 3.24: the reverse implication should recover dual optimality from a
subgradient of `valueFunction` at the origin. -/
lemma dualOptimalSolution_of_mem_subdifferentialValueFunctionZero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDualExists : ∃ y' : Fin m → ℝ, ∃ z' : Fin p → ℝ,
      IsDualOptimalSolution X f g A b fOpt y' z')
    (hSub :
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace))) :
    IsDualOptimalSolution X f g A b fOpt y z := by
  let _ := hf_ne_bot
  -- Route correction: the reverse implication now follows the textbook support-inequality route,
  -- but uses a real self-perturbation slice to avoid the ill-typed substitution
  -- `(u, t) = (g x, A x + b)`.
  rcases hDualExists with ⟨y', z', hDual'⟩
  have hLub : IsLUB (dualObjectiveValues X f g A b) (fOpt : EReal) := hDual'.2.2
  have hy_nonneg :
      ∀ i : Fin m, 0 ≤ y i :=
    multiplierNonneg_of_mem_subdifferentialValueFunctionZero
      X f g A b fOpt y z hPrimal hSub
  have hLower :
      (fOpt : EReal) ≤ lagrangianDualObjective X f g A b y z :=
    primalOptimalValue_le_lagrangianDualObjective_of_mem_subdifferentialValueFunctionZero
      X f g A b fOpt y z hg_ne_bot hPrimal hSub
  have hValueMem :
      lagrangianDualObjective X f g A b y z ∈ dualObjectiveValues X f g A b := by
    exact (mem_dualObjectiveValues X f g A b (lagrangianDualObjective X f g A b y z)).2
      ⟨y, z, hy_nonneg, rfl⟩
  have hUpper :
      lagrangianDualObjective X f g A b y z ≤ (fOpt : EReal) :=
    hLub.1 hValueMem
  have hValueEq :
      lagrangianDualObjective X f g A b y z = (fOpt : EReal) :=
    le_antisymm hUpper hLower
  exact ⟨hy_nonneg, hValueEq, hLub⟩

-- Semantic search note: `lean_leansearch` did not surface a more canonical existing theorem for
-- this source-facing value-function/subdifferential bridge, so the current owner/API split stays.
-- Proof sketch: dual attainment at the primal optimal value gives a multiplier pair whose affine
-- lower bound shows that the owner perturbation value function never takes the value `⊥`, while
-- the finite primal optimal value gives a finite value at `(0,0)`, hence a nonempty effective
-- domain.
/-- Properness clause for Theorem 3.24: if the finite primal optimal value is also attained by a
dual optimal solution, then the perturbation value function is proper. -/
theorem valueFunction_isProper_of_primalOptimalValue_and_dualOptimalSolution_exists
    (hX_nonempty : X.Nonempty)
    (hX : Convex ℝ X)
    (hf : is_convex_function f)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg : ∀ i : Fin m, is_convex_function (g i))
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDualExists : ∃ y : Fin m → ℝ, ∃ z : Fin p → ℝ, IsDualOptimalSolution X f g A b fOpt y z)
    :
    IsProperExtendedRealFunction (valueFunction X f g A b) := by
  let _ := hX_nonempty
  let _ := hX
  let _ := hf
  let _ := hf_ne_bot
  let _ := hg
  let _ := hg_ne_bot
  rcases hDualExists with ⟨y, z, hDual⟩
  have hzero :
      valueFunction X f g A b (0 : PerturbationSpace) = (fOpt : EReal) :=
    valueFunction_zero_eq_primalOptimalValue X f g A b fOpt hPrimal
  have hsub :
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace)) :=
    dualOptimalSolution_mem_subdifferentialValueFunctionZero X f g A b fOpt y z hPrimal hDual
  rw [mem_strongDualSubdifferential, mem_subdifferential] at hsub
  refine ⟨?_, ?_⟩
  · intro perturb
    -- Use the support inequality from the forward subgradient implication to rule out `⊥`.
    have hsupport :
        ((((fOpt + (negPerturbationDualPair y z perturb : ℝ)) : ℝ) : EReal)) ≤
          valueFunction X f g A b perturb := by
      simpa [hzero, EReal.coe_add, ge_iff_le] using hsub.2 perturb
    intro hbot
    simp [hbot] at hsupport
  · refine ⟨0, ?_⟩
    -- The primal optimal value gives a finite value at the origin, so the effective domain is
    -- nonempty.
    rw [mem_effective_domain, hzero]
    simp

-- Proof sketch: convexity follows from the owner theorem `value_function_is_convex` applied to
-- the Euclidean bridge of the primal data. The source theorem shares the same strong-duality and
-- dual-attainment preamble across all clauses, so that full context is kept explicit here even
-- though the canonical convexity owner theorem itself uses only the convexity assumptions.
/-- Convexity clause for Theorem 3.24: under the shared theorem preamble, the perturbation value
function is convex. -/
theorem valueFunction_is_convex_of_convex_primal_problem
    (hX_nonempty : X.Nonempty)
    (hX : Convex ℝ X)
    (hf : is_convex_function f)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg : ∀ i : Fin m, is_convex_function (g i))
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDualExists : ∃ y : Fin m → ℝ, ∃ z : Fin p → ℝ, IsDualOptimalSolution X f g A b fOpt y z)
    :
    is_convex_function (valueFunction X f g A b) := by
  let _ := hX_nonempty
  let _ := hf_ne_bot
  let _ := hg_ne_bot
  let _ := hPrimal
  let _ := hDualExists
  have hX_toLp : Convex ℝ (toLp 2 '' X) := by
    simpa using
      hX.linear_image ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap)
  have hf_ofLp : is_convex_function (fun x : EuclideanSpace ℝ (Fin n) ↦ f (ofLp x)) := by
    simpa using
      is_convex_function_precompose_linearMap_add
        hf
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
        (0 : Fin n → ℝ)
  have hg_ofLp :
      ∀ i : Fin m, is_convex_function (fun x : EuclideanSpace ℝ (Fin n) ↦ g i (ofLp x)) := by
    intro i
    simpa using
      is_convex_function_precompose_linearMap_add
        (hg i)
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
        (0 : Fin n → ℝ)
  -- Transport convexity to the owner perturbation value function on the Euclidean bridge.
  simpa [valueFunction] using
    value_function_is_convex
      (toLp 2 '' X)
      (fun x : EuclideanSpace ℝ (Fin n) ↦ f (ofLp x))
      (fun i x ↦ g i (ofLp x))
      A.toEuclideanLin
      (toLp 2 b)
      hf_ofLp
      hg_ofLp
      hX_toLp

-- Proof sketch: if `(y,z)` is dual optimal, the defining lower bound for the dual objective gives
-- the global affine support inequality for the owner perturbation value function at `(0,0)` with
-- supporting functional represented by `-(y,z)`. Conversely, a continuous-dual subgradient
-- inequality at `(0,0)` forces `y ≥ 0` by testing the standard basis perturbations and identifies
-- the dual objective value with the primal optimal value `fOpt`. The full strong-duality and
-- dual-attainment preamble is kept explicit on the exported source-facing statement.
/-- Characterization clause for Theorem 3.24: a multiplier pair `(y,z)` is a dual optimal
solution exactly when the negated pair represents a subgradient of the value function at the
origin. -/
theorem isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hX_nonempty : X.Nonempty)
    (hX : Convex ℝ X)
    (hf : is_convex_function f)
    (hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥)
    (hg : ∀ i : Fin m, is_convex_function (g i))
    (hg_ne_bot : ∀ i : Fin m, ∀ x : Fin n → ℝ, g i x ≠ ⊥)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDualExists : ∃ y' : Fin m → ℝ, ∃ z' : Fin p → ℝ, IsDualOptimalSolution X f g A b fOpt y' z')
    :
    IsDualOptimalSolution X f g A b fOpt y z ↔
      negPerturbationDualPair y z ∈
        ∂ₛ(valueFunction X f g A b)((0 : PerturbationSpace)) := by
  let _ := hX_nonempty
  let _ := hX
  let _ := hf
  let _ := hg
  constructor
  · intro hDual
    -- The forward direction is the source proof's affine lower-support argument.
    exact dualOptimalSolution_mem_subdifferentialValueFunctionZero
      X f g A b fOpt y z hPrimal hDual
  · intro hSub
    -- The reverse direction is isolated in a dedicated helper so the theorem statement stays
    -- stable while the remaining `⊥`-branch reconstruction work is finished.
    exact dualOptimalSolution_of_mem_subdifferentialValueFunctionZero
      X f g A b fOpt y z hf_ne_bot hg_ne_bot hPrimal hDualExists hSub

end Theorem_3_24

end
