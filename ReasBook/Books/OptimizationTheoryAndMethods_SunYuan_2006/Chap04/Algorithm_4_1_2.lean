/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Definition_4_1_1
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall: `lean_leansearch` surfaced the canonical `HasGradientAt` and `IsMinOn`
-- APIs, but no dedicated mathlib owner for the general conjugate direction method itself.
-- Following nearby repository precedent, this file records one concrete run of the algorithm.

open Matrix

/-- The ambient Euclidean space `ℝ^n` for conjugate direction methods. -/
abbrev ConjugateDirectionPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A source-facing record for Chapter04 Algorithm 4.1.2 on `ℝ^n` consists
of a tolerance `ε > 0`, an initial point `x₀`, iterates `x k`,
explicit gradient data `g k`, search directions `d k`, step sizes `α k`,
and a fixed matrix `G`. The initialization satisfies `x 0 = x₀`, `g 0`
is a gradient of `f` at `x 0`, and the initial direction is descent:
`(d 0)ᵀ g 0 < 0`. At every index `k`, `g k` is a gradient of `f` at `x k`;
at every nonterminal index with `ε < ‖g k‖`, `α k` is a source-facing exact
line-search step on the nonnegative ray from `x k` along `d k`, the next iterate
is `x (k + 1) = x k + α k • d k`, and the next direction satisfies the
`G`-conjugacy relations `(d (k + 1))ᵀ G (d j) = 0` for all `j ≤ k` and is
nonzero. -/
structure GeneralConjugateDirectionMethod (n : ℕ)
    (f : ConjugateDirectionPoint n → ℝ) where
  ε : ℝ
  x0 : ConjugateDirectionPoint n
  G : Matrix (Fin n) (Fin n) ℝ
  x : ℕ → ConjugateDirectionPoint n
  g : ℕ → ConjugateDirectionPoint n
  d : ℕ → ConjugateDirectionPoint n
  α : ℕ → ℝ
  eps_pos : 0 < ε
  x_zero : x 0 = x0
  hasGradientAt (k : ℕ) : HasGradientAt f (g k) (x k)
  initialDescent : dotProduct (d 0) (g 0) < 0
  exactLineSearch (k : ℕ) (hNotStopped : ε < ‖g k‖) :
      IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  update (k : ℕ) (hNotStopped : ε < ‖g k‖) :
      x (k + 1) = x k + α k • d k
  nextDirection_nonzero (k : ℕ) (hNotStopped : ε < ‖g k‖) :
      d (k + 1) ≠ 0
  conjugateDirections (k : ℕ) (hNotStopped : ε < ‖g k‖) (j : ℕ) (hj : j ≤ k) :
      dotProduct (d (k + 1)) (G.mulVec (d j)) = 0

/-- A general conjugate direction method can be used as its sequence of iterates. -/
instance {n : ℕ} {f : ConjugateDirectionPoint n → ℝ} :
    CoeFun (GeneralConjugateDirectionMethod n f) (fun _ ↦ ℕ → ConjugateDirectionPoint n) where
  coe A := A.x

/-- The initial descent condition forces the first search direction to be nonzero. -/
theorem GeneralConjugateDirectionMethod.direction_zero_ne {n : ℕ}
    {f : ConjugateDirectionPoint n → ℝ}
    (A : GeneralConjugateDirectionMethod n f) :
    A.d 0 ≠ 0 := by
  intro hd
  have hzero : dotProduct (A.d 0) (A.g 0) = 0 := by
    simp [hd]
  have : ¬ dotProduct (A.d 0) (A.g 0) < 0 := by
    simp [hzero]
  exact this A.initialDescent

/-- The stopping condition for Algorithm 4.1.2 at index `k` is `‖g k‖ ≤ ε`. -/
def GeneralConjugateDirectionMethod.terminatedAt {n : ℕ}
    {f : ConjugateDirectionPoint n → ℝ}
    (A : GeneralConjugateDirectionMethod n f) (k : ℕ) : Prop :=
  ‖A.g k‖ ≤ A.ε

/-- `terminatedAt` unfolds to the gradient-norm stopping test from Algorithm 4.1.2. -/
theorem GeneralConjugateDirectionMethod.terminatedAt_iff {n : ℕ}
    {f : ConjugateDirectionPoint n → ℝ}
    (A : GeneralConjugateDirectionMethod n f) (k : ℕ) :
    A.terminatedAt k ↔ ‖A.g k‖ ≤ A.ε :=
  Iff.rfl

/-- When `G` is positive definite, its bilinear form is symmetric on `ℝ^n`. -/
theorem GeneralConjugateDirectionMethod.dotProduct_mulVec_comm {n : ℕ}
    {f : ConjugateDirectionPoint n → ℝ}
    (A : GeneralConjugateDirectionMethod n f) [Fact A.G.PosDef]
    (u v : ConjugateDirectionPoint n) :
    dotProduct u (A.G.mulVec v) = dotProduct v (A.G.mulVec u) := by
  have hPosDef : A.G.PosDef := Fact.out
  have hsymm : A.G.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using (show A.G.IsHermitian from hPosDef.1)
  simpa [hsymm.eq] using Matrix.dotProduct_transpose_mulVec A.G u v

/-- If the first `m` directions come from nonterminal steps, then they form a canonical
`G`-conjugate family in the sense of Definition 4.1.1 whenever `G` is positive definite. -/
theorem GeneralConjugateDirectionMethod.isConjugateFamily_prefix {n : ℕ}
    {f : ConjugateDirectionPoint n → ℝ}
    (A : GeneralConjugateDirectionMethod n f) [Fact A.G.PosDef] {m : ℕ}
    (hactive : ∀ j : ℕ, j + 1 < m → A.ε < ‖A.g j‖) :
    A.G.IsConjugateFamily (fun i : Fin m ↦ A.d i) := by
  rw [Matrix.isConjugateFamily_iff]
  constructor
  · intro i
    rcases Nat.eq_zero_or_pos i.1 with hzero | hi
    · have hm : 0 < m := by
        simpa [hzero] using i.is_lt
      have hi0 : i = ⟨0, hm⟩ := by
        apply Fin.ext
        simp [hzero]
      cases hi0
      simpa using A.direction_zero_ne
    · have him : i.1 - 1 + 1 < m := by
        simp [Nat.sub_add_cancel hi, i.is_lt]
      simpa [Nat.sub_add_cancel hi] using
        A.nextDirection_nonzero (i.1 - 1) (hactive (i.1 - 1) him)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
    · have hjm : j.1 - 1 + 1 < m := by
        have hjpos : 0 < j.1 := lt_of_le_of_lt (Nat.zero_le i.1) (show i.1 < j.1 from hij_lt)
        simp [Nat.sub_add_cancel hjpos, j.is_lt]
      have hjpos : 0 < j.1 := lt_of_le_of_lt (Nat.zero_le i.1) (show i.1 < j.1 from hij_lt)
      have hij_le : i.1 ≤ j.1 - 1 := by
        exact Nat.lt_succ_iff.mp (by simpa [Nat.sub_add_cancel hjpos] using hij_lt)
      have horth :
          dotProduct (A.d j) (A.G.mulVec (A.d i)) = 0 := by
        simpa [Nat.sub_add_cancel hjpos] using
        A.conjugateDirections (j.1 - 1) (hactive (j.1 - 1) hjm) i.1
          hij_le
      rw [← A.dotProduct_mulVec_comm (A.d i) (A.d j)] at horth
      exact horth
    · have him : i.1 - 1 + 1 < m := by
        have hipos : 0 < i.1 := lt_of_le_of_lt (Nat.zero_le j.1) (show j.1 < i.1 from hij_gt)
        simp [Nat.sub_add_cancel hipos, i.is_lt]
      have hipos : 0 < i.1 := lt_of_le_of_lt (Nat.zero_le j.1) (show j.1 < i.1 from hij_gt)
      have hij_le : j.1 ≤ i.1 - 1 := by
        exact Nat.lt_succ_iff.mp (by simpa [Nat.sub_add_cancel hipos] using hij_gt)
      simpa [Nat.sub_add_cancel hipos] using
        A.conjugateDirections (i.1 - 1) (hactive (i.1 - 1) him) j.1 hij_le

/-- Chapter04 Algorithm 4.1.2: a nonterminal step uses exact line search, the iterate update, and a
nonzero `G`-conjugate next direction. -/
theorem GeneralConjugateDirectionMethod.nonterminalStep {n : ℕ}
    {f : ConjugateDirectionPoint n → ℝ}
    (A : GeneralConjugateDirectionMethod n f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    IsExactLineSearchStepOnNonnegativeRay f (A.x k) (A.d k) (A.α k) ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      A.d (k + 1) ≠ 0 ∧
      ∀ j : ℕ, j ≤ k →
        dotProduct (A.d (k + 1)) (A.G.mulVec (A.d j)) = 0 := by
  -- Package the nonterminal-step data directly from the structure fields.
  refine ⟨A.exactLineSearch k hNotStopped,
    A.update k hNotStopped,
    A.nextDirection_nonzero k hNotStopped,
    ?_⟩
  -- The remaining conjunct is exactly the stored conjugacy relation.
  intro j hj
  exact A.conjugateDirections k hNotStopped j hj
