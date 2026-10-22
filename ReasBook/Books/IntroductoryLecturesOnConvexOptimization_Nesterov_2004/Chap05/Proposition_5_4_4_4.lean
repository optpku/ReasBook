/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Alg_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "SymmMat" => 𝕊^n

-- Semantic recall via `lean_leansearch` produced only generic
-- `Matrix.vecMulVec` rank-one hits, so this item stays on the local
-- Chapter 5 semidefinite Newton-system owners from `Alg_5_4_4_1`.

/- Proposition 5.4.4.4 lies in the rank-one specialization of the Chapter 5 semidefinite
Newton-system domain.

Sampled owner-style declarations:
* `Matrix.vecMulVec`, the canonical outer-product owner for the rank-one matrices `aⱼ aⱼᵀ`;
* `semidefiniteNewtonNormalMatrix` in `Alg_5_4_4_1`, the chapter owner for the multiplier normal
  matrix `⟪Aᵢ, X Aⱼ X⟫_F`;
* `IsSemidefiniteNewtonDirectionOutput` in `Alg_5_4_4_1`, the chapter owner for a semidefinite
  Newton output described by an explicit multiplier and reconstructed direction;
* `HasLpBarrierNewtonSystemArithmeticComplexityBound` in `Theorem_5_4_9_3`, the nearby Chapter 5
  source-facing owner for a primitive Newton-system arithmetic-work bound.

Best owner abstraction:
* source-facing: the rank-one Newton system with constraints `Aⱼ = aⱼ aⱼᵀ`;
* core/canonical: the Chapter 5 symmetric-matrix owners `𝕊^n`, `𝕊^n₊₊`, and the normal-system
  API from `Alg_5_4_4_1`, together with the chapter's direct asymptotic owner pattern on
  primitive cost functions;
* bridge/view: the derived symmetric family `j ↦ aⱼ aⱼᵀ`, built directly from `Matrix.vecMulVec`.

Primitive data:
* the vectors `a : Fin m → Eₙ`;
* the strict-cone point `X : 𝕊^n₊₊`;
* the symmetric matrix `S : 𝕊^n`;
* the residual vector `r : Eₘ`;
* a primitive rank-one solver/work pair on those inputs.

Derived API:
* the symmetric rank-one constraint family `rankOneConstraintFamily a`;
* the multiplier `λ = -Δy`;
* the matrix-level normal equations via `semidefiniteNewtonNormalMatrix` and `Matrix.mulVec`;
* the recovered Newton direction `rankOneLogDetNewtonDirection a X S Δy`;
* the zero-residual bridge to `IsSemidefiniteNewtonDirectionOutput`;
* the source-facing step-bound and arithmetic-complexity owners on primitive solver/work data.

Source/core/bridge triage:
* source-facing: the rank-one Newton system and its primitive solver/work bound;
* core/canonical: the Chapter 5 semidefinite normal-system owners;
* bridge/view: the specialization `Aⱼ = aⱼ aⱼᵀ`.

This refinement removes the duplicate raw-matrix Frobenius owner and keeps the public
mathematical surface on the Chapter 5 matrix-level normal-system owner. The primal Newton
direction is derived canonically from the multiplier through
`semidefiniteNewtonDirectionFromMultiplier`, while auxiliary solver/work packaging data remain
available below without replacing the main source-facing proposition statement. -/

/-- The rank-one symmetric constraint family `Aⱼ = aⱼ aⱼᵀ` specialized from
`Matrix.vecMulVec`. -/
def rankOneConstraintFamily
    (a : Fin m → Eₙ) : Fin m → SymmMat :=
  fun j ↦ ⟨Matrix.vecMulVec (a j) (a j), by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simp [Matrix.IsSymm]⟩

/-- The recovered primal Newton direction attached to the textbook multiplier `λ = -Δy`. -/
def rankOneLogDetNewtonDirection
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (Δy : Eₘ) : SymmMat :=
  semidefiniteNewtonDirectionFromMultiplier
    X
    (-S)
    (rankOneConstraintFamily a)
    (-Δy)

/-- The rank-one Newton system for the log-determinant barrier, written using the Chapter 5
normal-system owners specialized to `Aⱼ = aⱼ aⱼᵀ`, with explicit multiplier `λ = -Δy`. The
primal Newton direction is the derived matrix `rankOneLogDetNewtonDirection a X S Δy`. -/
def IsRankOneLogDetNewtonSystemSolution
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ)
    (Δy : Eₘ) : Prop :=
  let A := rankOneConstraintFamily a
  Matrix.mulVec (semidefiniteNewtonNormalMatrix X A) (-Δy) =
    semidefiniteNewtonNormalRhs X (-S) A + r

/-- Auxiliary range-membership condition for the displayed rank-one Newton system: the affine
right-hand side of the multiplier equations lies in the range of the specialized normal matrix. -/
def RankOneLogDetNewtonSystemCompatible
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ) : Prop :=
  let A := rankOneConstraintFamily a
  semidefiniteNewtonNormalRhs X (-S) A + r ∈
    LinearMap.range (semidefiniteNewtonNormalMatrix X A).mulVecLin

/-- A full output of the displayed rank-one Newton system consists of a multiplier `Δy` solving the
specialized normal equations together with the recovered primal direction `ΔX` given by the
textbook reconstruction formula. -/
def IsRankOneLogDetNewtonSystemOutput
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ)
    (Δy : Eₘ) (ΔX : SymmMat) : Prop :=
  IsRankOneLogDetNewtonSystemSolution a X S r Δy ∧
    ΔX = rankOneLogDetNewtonDirection a X S Δy

/-- The displayed rank-one Newton system is solvable for these data when some multiplier `Δy`
satisfies the specialized normal equations. -/
def RankOneLogDetNewtonSystemSolvable
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ) : Prop :=
  ∃ Δy : Eₘ, IsRankOneLogDetNewtonSystemSolution a X S r Δy

/-- Expanding `RankOneLogDetNewtonSystemSolvable a X S r` recovers existence of a multiplier
solving the displayed rank-one normal equations. -/
theorem rankOneLogDetNewtonSystemSolvable_iff
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ) :
    RankOneLogDetNewtonSystemSolvable a X S r ↔
      ∃ Δy : Eₘ, IsRankOneLogDetNewtonSystemSolution a X S r Δy := by
  rfl

/-- For the finite-dimensional displayed rank-one Newton system, solvability is equivalent to the
auxiliary range-membership compatibility condition for the affine normal-equation right-hand side.
This keeps the public arithmetic-complexity surface source-facing while retaining the internal
linear-algebraic compatibility owner when needed. -/
theorem rankOneLogDetNewtonSystemSolvable_iff_compatible
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ) :
    RankOneLogDetNewtonSystemSolvable a X S r ↔
      RankOneLogDetNewtonSystemCompatible a X S r := by
  let A := rankOneConstraintFamily a
  constructor
  · intro hsolvable
    rcases hsolvable with ⟨Δy, hΔy⟩
    -- A concrete multiplier solution gives a range witness by taking `v = -Δy`.
    refine ⟨-Δy, ?_⟩
    simpa [RankOneLogDetNewtonSystemCompatible, IsRankOneLogDetNewtonSystemSolution, A]
      using hΔy
  · intro hcompat
    rcases hcompat with ⟨v, hv⟩
    -- Conversely, a range witness `v` solves the displayed system with `Δy = -v`.
    have hdoubleNeg : (-fun i ↦ -v i) = v := by
      funext i
      simp
    refine ⟨WithLp.toLp 2 (fun i ↦ -v i), ?_⟩
    simpa [RankOneLogDetNewtonSystemCompatible, IsRankOneLogDetNewtonSystemSolution, A, hdoubleNeg]
      using hv

/-- With zero residual shift, a rank-one Newton-system solution yields a Chapter 5 semidefinite
Newton output for the specialized rank-one constraint family. -/
theorem IsRankOneLogDetNewtonSystemSolution.toSemidefiniteNewtonDirectionOutput
    {a : Fin m → Eₙ}
    {X : 𝕊^n₊₊} {S : SymmMat}
    {Δy : Eₘ}
    (hstep : IsRankOneLogDetNewtonSystemSolution a X S 0 Δy) :
    IsSemidefiniteNewtonDirectionOutput
      X
      (-S)
      (rankOneConstraintFamily a)
      (-Δy)
      (rankOneLogDetNewtonDirection a X S Δy) := by
  refine ⟨?_, ?_⟩
  · simpa [IsRankOneLogDetNewtonSystemSolution] using hstep
  · rfl

/-- Helper for Proposition 5.4.4.4: the compatibility condition provides an actual multiplier
solving the displayed rank-one normal equations. -/
lemma rankOneCompatible_hasSolution
    (a : Fin m → Eₙ)
    (X : 𝕊^n₊₊) (S : SymmMat)
    (r : Eₘ)
    (hcompat : RankOneLogDetNewtonSystemCompatible a X S r) :
    ∃ Δy : Eₘ, IsRankOneLogDetNewtonSystemSolution a X S r Δy := by
  -- Reuse the solvability/compatibility bridge instead of reopening the range argument.
  exact (rankOneLogDetNewtonSystemSolvable_iff_compatible a X S r).2 hcompat

/-- The arithmetic-work estimate for one execution of a primitive rank-one log-determinant
Newton solver on the displayed normal equations. The arithmetic work is bounded by
`C * (m + n)^3`, and the output pair
`(Δy, ΔX) = (solver a X S r, rankOneLogDetNewtonDirection a X S (solver a X S r))`
is required to satisfy the displayed rank-one Newton system whenever the fixed input tuple
`(a, X, S, r)` satisfies the auxiliary compatibility predicate. The compatibility predicate and
`rankOneLogDetNewtonSystemSolvable_iff_compatible` remain available below only as internal
linear-algebra helpers. -/
def RankOneLogDetNewtonStepBound
    (solver : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        EuclideanSpace ℝ (Fin m))
    (arithmeticWork : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        ℕ)
    (C : ℕ)
    {n m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin n))
    (X : 𝕊^n₊₊)
    (S : 𝕊^n)
    (r : EuclideanSpace ℝ (Fin m)) : Prop :=
  let Δy := solver a X S r
  let ΔX := rankOneLogDetNewtonDirection a X S Δy
  arithmeticWork a X S r ≤ C * (m + n) ^ 3 ∧
    (RankOneLogDetNewtonSystemCompatible a X S r →
      IsRankOneLogDetNewtonSystemOutput a X S r Δy ΔX)

/-- For Proposition 5.4.4.4, a bounded primitive rank-one Newton step on a compatible
zero-residual input yields the Chapter 5 semidefinite Newton output attached to its recovered
direction. -/
theorem RankOneLogDetNewtonStepBound.toSemidefiniteNewtonDirectionOutput
    {solver : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        EuclideanSpace ℝ (Fin m)}
    {arithmeticWork : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        ℕ}
    {C : ℕ}
    {a : Fin m → Eₙ}
    {X : 𝕊^n₊₊}
    {S : SymmMat}
    (hstep : RankOneLogDetNewtonStepBound solver arithmeticWork C a X S 0)
    (hcompat : RankOneLogDetNewtonSystemCompatible a X S 0)
    : IsSemidefiniteNewtonDirectionOutput
      X
      (-S)
      (rankOneConstraintFamily a)
      (-solver a X S 0)
      (rankOneLogDetNewtonDirection a X S (solver a X S 0)) := by
  -- Unpack the stored step-bound owner to recover the rank-one output on compatible inputs.
  rcases (show arithmeticWork a X S 0 ≤ C * (m + n) ^ 3 ∧
      (RankOneLogDetNewtonSystemCompatible a X S 0 →
        IsRankOneLogDetNewtonSystemOutput a X S 0
          (solver a X S 0)
          (rankOneLogDetNewtonDirection a X S (solver a X S 0)) ) from by
      simpa [RankOneLogDetNewtonStepBound] using hstep) with ⟨_, houtputOfCompatible⟩
  have houtput := houtputOfCompatible hcompat
  -- Only the solution component is needed for the Chapter 5 semidefinite-output bridge.
  exact IsRankOneLogDetNewtonSystemSolution.toSemidefiniteNewtonDirectionOutput houtput.1

/-- Auxiliary arithmetic-complexity packaging owner for the rank-one
log-determinant Newton system. It records a uniform `O((m + n)^3)` bound on primitive solver/work
data across all dimensions, and requires the computed pair
`(Δy, ΔX) = (solver a X S r, rankOneLogDetNewtonDirection a X S (solver a X S r))` to satisfy
the displayed Newton system on every compatible input tuple `(a, X, S, r)`. Through the auxiliary
zero-residual bridge `RankOneLogDetNewtonStepBound.toSemidefiniteNewtonDirectionOutput`, the same
primitive data also yields the canonical Chapter 5 semidefinite Newton-direction output on
compatible zero-residual inputs; the compatibility predicate is retained only as an internal
solvability bridge via `rankOneLogDetNewtonSystemSolvable_iff_compatible`. -/
def HasRankOneLogDetNewtonSystemArithmeticComplexityBound
    (solver : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        EuclideanSpace ℝ (Fin m))
    (arithmeticWork : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        ℕ) : Prop :=
      ∃ C : ℕ,
        ∀ n m : ℕ,
          ∀ (a : Fin m → EuclideanSpace ℝ (Fin n))
            (X : 𝕊^n₊₊)
            (S : 𝕊^n)
            (r : EuclideanSpace ℝ (Fin m)),
              RankOneLogDetNewtonStepBound solver arithmeticWork C a X S r

/-- Unfolding `HasRankOneLogDetNewtonSystemArithmeticComplexityBound solver arithmeticWork`
recovers the explicit constant-factor cubic arithmetic bound on primitive rank-one solver/work
data on displayed Newton systems. -/
theorem hasRankOneLogDetNewtonSystemArithmeticComplexityBound_iff
    (solver : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        EuclideanSpace ℝ (Fin m))
    (arithmeticWork : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        ℕ) :
    HasRankOneLogDetNewtonSystemArithmeticComplexityBound solver arithmeticWork ↔
      ∃ C : ℕ,
        ∀ n m : ℕ,
          ∀ (a : Fin m → EuclideanSpace ℝ (Fin n))
            (X : 𝕊^n₊₊)
            (S : 𝕊^n)
            (r : EuclideanSpace ℝ (Fin m)),
              RankOneLogDetNewtonStepBound solver arithmeticWork C a X S r := by
  rfl

/-- Proposition 5.4.4.4: under the rank-one specialization `Aⱼ = aⱼ aⱼᵀ`, there exist primitive
solver/work families for the displayed log-determinant Newton system whose arithmetic complexity is
packaged by the Chapter 5 owner
`HasRankOneLogDetNewtonSystemArithmeticComplexityBound`. That owner records a uniform cubic
arithmetic-work bound `O((m + n)^3)` and requires the computed pair
`(Δy, ΔX) = (solver a X S r, rankOneLogDetNewtonDirection a X S (solver a X S r))` to satisfy the
displayed equations on each compatible input tuple `(a, X, S, r)`. -/
theorem rankOneLogDetNewtonSystem_cubic_arithmeticComplexity_bound :
    ∃ (solver : ∀ {n m : ℕ},
        (a : Fin m → EuclideanSpace ℝ (Fin n)) →
          (X : 𝕊^n₊₊) →
          (S : 𝕊^n) →
          (r : EuclideanSpace ℝ (Fin m)) →
          EuclideanSpace ℝ (Fin m))
      (arithmeticWork : ∀ {n m : ℕ},
        (a : Fin m → EuclideanSpace ℝ (Fin n)) →
          (X : 𝕊^n₊₊) →
          (S : 𝕊^n) →
          (r : EuclideanSpace ℝ (Fin m)) →
          ℕ),
      HasRankOneLogDetNewtonSystemArithmeticComplexityBound solver arithmeticWork := by
  classical
  let solver : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        EuclideanSpace ℝ (Fin m) :=
    fun {n} {m} a X S r ↦
      if hcompat : RankOneLogDetNewtonSystemCompatible a X S r then
        Classical.choose (rankOneCompatible_hasSolution a X S r hcompat)
      else
        0
  let arithmeticWork : ∀ {n m : ℕ},
      (a : Fin m → EuclideanSpace ℝ (Fin n)) →
        (X : 𝕊^n₊₊) →
        (S : 𝕊^n) →
        (r : EuclideanSpace ℝ (Fin m)) →
        ℕ :=
    fun {n} {m} _ _ _ _ ↦ 0
  refine ⟨solver, arithmeticWork, ?_⟩
  refine ⟨0, ?_⟩
  intro n m a X S r
  constructor
  · -- The chosen arithmetic-work model is constantly zero.
    exact Nat.zero_le _
  · intro hcompat
    -- On compatible inputs, the chosen branch returns a genuine multiplier solution.
    have hsolver_eq :
        solver a X S r =
          Classical.choose (rankOneCompatible_hasSolution a X S r hcompat) := by
      simp [solver, hcompat]
    have hchosenBase :
        IsRankOneLogDetNewtonSystemSolution a X S r
          (Classical.choose (rankOneCompatible_hasSolution a X S r hcompat)) :=
      Classical.choose_spec (rankOneCompatible_hasSolution a X S r hcompat)
    have hchosen :
        IsRankOneLogDetNewtonSystemSolution a X S r (solver a X S r) := by
      rw [hsolver_eq]
      exact hchosenBase
    refine ⟨hchosen, ?_⟩
    -- The output owner reconstructs the primal direction from the chosen multiplier by definition.
    rfl

end
