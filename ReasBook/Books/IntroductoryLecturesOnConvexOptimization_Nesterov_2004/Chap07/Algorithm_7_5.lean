/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Algorithm 7.5 lies in the centrally symmetric rounding / positive-definite matrix norm domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` and `positiveDefMatrixNorm_dualNorm_apply` in `Definition_7_23`, the
  chapter owner of the weighted norm and its dual support-function formula;
- `centralSymmetryRoundingAlphaStar` in `Proposition_7_8`, the chapter owner of the scalar update
  coefficient as a function of the normalized squared dual radius;
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner from mathlib.

Best owner abstraction:
- source-facing: the algorithm run, its bodywise maximal dual radius, and the rank-one matrix
  update;
- core/canonical: `positiveDefMatrixNorm`, its dual norm `‖·‖[G,*]`,
  `centralSymmetryRoundingAlphaStar`, and `Matrix.vecMulVec`;
- bridge/view: the supremum formulas below relating the source-facing radius and coefficient to
  those canonical owners.

Primitive data:
- a convex body `C`;
- a positive-definite matrix owner `G : {G : Mat // G.PosDef}`;
- the matrix sequence and positivity witness in the algorithm record;
- the selected maximizers in `C`.

Derived API:
- the `G`-dual norm is the existing Chapter 7 owner `‖·‖[G,*]`;
- the maximal dual radius is the supremum of that owner over `C`;
- the update coefficient is obtained from the canonical scalar owner
  `centralSymmetryRoundingAlphaStar`.

The duplicate wheel in the previous version was the local dual-norm owner on arbitrary matrices.
This refinement moves that surface back to the existing Chapter 7 positive-definite-matrix owner
and keeps only the genuinely source-facing algorithm layer here. -/

/- Algorithm 7.5 reuses the Chapter 7 weighted dual-norm owner. -/
recall positiveDefMatrixNorm_dualNorm_apply

/-- The rank-one update `G ↦ (1 - α) G + α ggᵀ` used by the centrally symmetric rounding
algorithm. -/
def centralSymmetricRoundingUpdatedMatrix
    (G : Mat) (g : E) (α : ℝ) : Mat :=
  (1 - α) • G + α • Matrix.vecMulVec g g

-- Proof sketch: unfold `centralSymmetricRoundingUpdatedMatrix`.
/-- Expanding `centralSymmetricRoundingUpdatedMatrix G g α` gives `(1 - α) G + α ggᵀ`. -/
theorem centralSymmetricRoundingUpdatedMatrix_eq
    (G : Mat) (g : E) (α : ℝ) :
    centralSymmetricRoundingUpdatedMatrix G g α =
      (1 - α) • G + α • Matrix.vecMulVec g g :=
  rfl

/-- The maximal `G`-dual norm attained on the convex body `C`, namely
`max {‖g‖*_{G} : g ∈ C}` written as a supremum over `C`. -/
def centralSymmetricRoundingRadius
    (C : ConvexBody E) (G : { G : Mat // G.PosDef }) : ℝ :=
  sSup ((fun g : E ↦ ‖g‖[G,*]) '' (C : Set E))

-- Proof sketch: unfold `centralSymmetricRoundingRadius`; the right-hand side is exactly the
-- supremum of `g ↦ ‖g‖*_{G}` over the convex body `C`.
/-- Evaluating `centralSymmetricRoundingRadius C G` gives the supremum of `‖g‖*_{G}` over `g ∈ C`.
-/
theorem centralSymmetricRoundingRadius_eq_sSup
    (C : ConvexBody E) (G : { G : Mat // G.PosDef }) :
    centralSymmetricRoundingRadius C G =
      sSup ((fun g : E ↦ ‖g‖[G,*]) '' (C : Set E)) :=
  rfl

/-- The update coefficient
`α = (r² - n) / (n (r² - 1))` computed from the maximal dual radius `r`. -/
def centralSymmetricRoundingAlpha
    (C : ConvexBody E) (G : { G : Mat // G.PosDef }) : ℝ :=
  centralSymmetryRoundingAlphaStar n
    (((centralSymmetricRoundingRadius C G) ^ (2 : ℕ)) / (n : ℝ) - 1)

-- Proof sketch: unfold `centralSymmetricRoundingAlpha`; this is exactly the textbook formula with
-- `r = centralSymmetricRoundingRadius C G`, then simplify the scalar owner from
-- `Proposition_7_8`. The positivity assumption on the dimension excludes the degenerate case
-- `n = 0`, where the closed form is not valid.
/-- In positive dimension, evaluating `centralSymmetricRoundingAlpha C G` gives the textbook
coefficient `(r² - n) / (n (r² - 1))` with `r = centralSymmetricRoundingRadius C G`. -/
theorem centralSymmetricRoundingAlpha_eq
    (C : ConvexBody E) (G : { G : Mat // G.PosDef }) (hn : 1 ≤ n) :
    centralSymmetricRoundingAlpha C G =
      ((centralSymmetricRoundingRadius C G) ^ (2 : ℕ) - n) /
        ((n : ℝ) * ((centralSymmetricRoundingRadius C G) ^ (2 : ℕ) - 1)) := by
  -- Convert the positive-dimension hypothesis into the nonvanishing scalar denominator `n ≠ 0`.
  have hn' : (0 : ℝ) < n := by
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
  -- Route correction: keep the proof at the scalar-owner level and normalize the specialized
  -- `centralSymmetryRoundingAlphaStar` formula without unfolding the radius definition.
  rw [centralSymmetricRoundingAlpha, centralSymmetryRoundingAlphaStar]
  -- Clear the unique nontrivial denominator `n` and finish the remaining polynomial identity.
  field_simp [hn0]
  ring

/-- Algorithm 7.5: a run of the centrally symmetric rounding algorithm on a convex body `C`
consists of a positive-definite matrix sequence `Gₖ` and selected maximizers `gₖ ∈ C` such that
`gₖ` attains the maximal `Gₖ`-dual norm on `C`, the initial matrix is the prescribed `G₀`, and
whenever `rₖ = max_{g ∈ C} ‖g‖*_{Gₖ}` exceeds `γ √n` the next matrix is updated by
`Gₖ₊₁ = (1 - αₖ) Gₖ + αₖ gₖ gₖᵀ` with
`αₖ = (rₖ² - n) / (n (rₖ² - 1))`. -/
structure CentralSymmetricRoundingMethod (n : ℕ) where
  /-- Algorithm 7.5 is only meaningful in positive dimension. -/
  one_le_dim : 1 ≤ n
  /-- The convex body `C ⊆ ℝⁿ` to be rounded. -/
  body : ConvexBody (EuclideanSpace ℝ (Fin n))
  /-- The central symmetry assumption on `C`, encoded as balancedness about the origin. -/
  body_balanced : Balanced ℝ (body : Set (EuclideanSpace ℝ (Fin n)))
  /-- The target rounding parameter `γ > 1`. -/
  gamma : ℝ
  /-- The algorithm assumes `γ > 1`. -/
  one_lt_gamma : 1 < gamma
  /-- The prescribed initial positive-definite matrix `G₀`. -/
  initialMatrix : Matrix (Fin n) (Fin n) ℝ
  /-- The matrix sequence `Gₖ`. -/
  matrix : ℕ → Matrix (Fin n) (Fin n) ℝ
  /-- The selected maximizers `gₖ ∈ C`. -/
  maximizer : ℕ → EuclideanSpace ℝ (Fin n)
  /-- Every matrix `Gₖ` is positive definite, so the corresponding weighted dual norm is well
  defined. -/
  matrix_posDef : ∀ k : ℕ, (matrix k).PosDef
  /-- The sequence starts from the prescribed initial matrix `G₀`. -/
  matrix_zero : matrix 0 = initialMatrix
  /-- For each `k`, the selected point `gₖ` lies in `C` and maximizes `g ↦ ‖g‖*_{Gₖ}` on `C`. -/
  maximizer_isMaxOn :
    ∀ k : ℕ,
      let G : { G : Matrix (Fin n) (Fin n) ℝ // G.PosDef } := ⟨matrix k, matrix_posDef k⟩
      maximizer k ∈ (body : Set (EuclideanSpace ℝ (Fin n))) ∧
        IsMaxOn (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖g‖[G,*])
          (body : Set (EuclideanSpace ℝ (Fin n))) (maximizer k)
  /-- Whenever the current maximal dual radius `rₖ` is larger than `γ √n`, the algorithm performs
  the rank-one update with the textbook coefficient `αₖ`. -/
  matrix_succ_of_gt_threshold :
    ∀ k : ℕ,
      let G : { G : Matrix (Fin n) (Fin n) ℝ // G.PosDef } := ⟨matrix k, matrix_posDef k⟩
      gamma * Real.sqrt (n : ℝ) < centralSymmetricRoundingRadius body G →
        matrix (k + 1) =
          centralSymmetricRoundingUpdatedMatrix (matrix k) (maximizer k)
            (centralSymmetricRoundingAlpha body G)

namespace CentralSymmetricRoundingMethod

/-- A centrally symmetric rounding method can be used as its underlying matrix sequence
`G₀, G₁, G₂, ...`. -/
instance : CoeFun (CentralSymmetricRoundingMethod n)
    (fun _ ↦ ℕ → Matrix (Fin n) (Fin n) ℝ) where
  coe method := method.matrix

/-- The maximal dual radius `rₖ` attached to the `k`-th matrix of the method. -/
def radius (method : CentralSymmetricRoundingMethod n) (k : ℕ) : ℝ :=
  centralSymmetricRoundingRadius method.body ⟨method.matrix k, method.matrix_posDef k⟩

-- Proof sketch: unfold `CentralSymmetricRoundingMethod.radius`.
/-- The radius `method.radius k` is the maximal `Gₖ`-dual norm over the body `C`. -/
theorem radius_eq
    (method : CentralSymmetricRoundingMethod n) (k : ℕ) :
    method.radius k =
      centralSymmetricRoundingRadius method.body ⟨method.matrix k, method.matrix_posDef k⟩ :=
  rfl

/-- The update coefficient `αₖ` attached to the `k`-th matrix of the method. -/
def alpha (method : CentralSymmetricRoundingMethod n) (k : ℕ) : ℝ :=
  centralSymmetricRoundingAlpha method.body ⟨method.matrix k, method.matrix_posDef k⟩

-- Proof sketch: unfold `CentralSymmetricRoundingMethod.alpha`.
/-- The coefficient `method.alpha k` is the textbook quantity
`(rₖ² - n) / (n (rₖ² - 1))` computed from `method.radius k`. -/
theorem alpha_eq
    (method : CentralSymmetricRoundingMethod n) (k : ℕ) :
    method.alpha k =
      centralSymmetricRoundingAlpha method.body ⟨method.matrix k, method.matrix_posDef k⟩ :=
  rfl

/-- The stopping predicate `rₖ ≤ γ √n` from Algorithm 7.5. -/
def stoppingCriterion (method : CentralSymmetricRoundingMethod n) (k : ℕ) : Prop :=
  method.radius k ≤ method.gamma * Real.sqrt (n : ℝ)

/-- Algorithm 7.5 terminates when some iterate satisfies the threshold `rₖ ≤ γ √n`. -/
def Terminates (method : CentralSymmetricRoundingMethod n) : Prop :=
  ∃ k : ℕ, method.stoppingCriterion k

/-- The textbook first stopping index, derived canonically from the least iterate satisfying the
Algorithm 7.5 stopping predicate. -/
noncomputable def stoppingIndex
    {method : CentralSymmetricRoundingMethod n}
    (hTerminate : method.Terminates) : ℕ := by
  classical
  exact Nat.find hTerminate

/-- The first stopping index is least with respect to the stopping predicate. -/
theorem stoppingIndex_isLeast
    {method : CentralSymmetricRoundingMethod n}
    (hTerminate : method.Terminates) :
    IsLeast
      {k : ℕ | method.stoppingCriterion k}
      (method.stoppingIndex hTerminate) := by
  classical
  simpa [stoppingIndex] using Nat.isLeast_find hTerminate

/-- The stopping test succeeds at the first accepted iterate. -/
theorem stoppingIndex_spec
    {method : CentralSymmetricRoundingMethod n}
    (hTerminate : method.Terminates) :
    method.stoppingCriterion (method.stoppingIndex hTerminate) :=
  (method.stoppingIndex_isLeast hTerminate).1

/-- The stopping test fails at every earlier iterate. -/
theorem stoppingIndex_min
    {method : CentralSymmetricRoundingMethod n}
    (hTerminate : method.Terminates) {k : ℕ}
    (hk : k < method.stoppingIndex hTerminate) :
    ¬ method.stoppingCriterion k := by
  exact fun hkStop ↦
    (not_le_of_gt hk) ((method.stoppingIndex_isLeast hTerminate).2 hkStop)

/-- Before the first stopping index, the continuation inequality `γ √n < rₖ` holds. -/
theorem threshold_lt_radius_of_lt_stoppingIndex
    {method : CentralSymmetricRoundingMethod n}
    (hTerminate : method.Terminates) {k : ℕ}
    (hk : k < method.stoppingIndex hTerminate) :
    method.gamma * Real.sqrt (n : ℝ) < method.radius k := by
  exact lt_of_not_ge <| by
    simpa [stoppingCriterion] using
      (method.stoppingIndex_min hTerminate hk)

/-- Before the first stopping index, the next matrix is given by the textbook rank-one update. -/
theorem matrix_succ_of_lt_stoppingIndex
    {method : CentralSymmetricRoundingMethod n}
    (hTerminate : method.Terminates) {k : ℕ}
    (hk : k < method.stoppingIndex hTerminate) :
    method (k + 1) =
      centralSymmetricRoundingUpdatedMatrix (method k) (method.maximizer k) (method.alpha k) := by
  simpa [alpha, radius] using
    method.matrix_succ_of_gt_threshold k
      (method.threshold_lt_radius_of_lt_stoppingIndex hTerminate hk)

end CentralSymmetricRoundingMethod

end
