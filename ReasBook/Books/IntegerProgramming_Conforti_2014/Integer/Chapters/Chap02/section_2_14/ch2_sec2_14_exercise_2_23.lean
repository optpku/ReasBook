/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Interval.Set.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: `lean_leansearch` is unavailable in this runner, so this file uses
-- source-faithful local notions for explicit piecewise-linear descriptions and MILP formulations.

/-- A finite interval cover on which a real-valued function is affine. -/
structure PiecewiseLinearOnInterval (l u : ℝ) (f : ℝ → ℝ) where
  pieces : ℕ
  lower : Fin pieces → ℝ
  upper : Fin pieces → ℝ
  slope : Fin pieces → ℝ
  intercept : Fin pieces → ℝ
  lower_le_upper : ∀ j, lower j ≤ upper j
  cover : Set.Icc l u ⊆ ⋃ j, Set.Icc (lower j) (upper j)
  eq_affine : ∀ j x, x ∈ Set.Icc (lower j) (upper j) → f x = slope j * x + intercept j

/-- The separable objective function `x ↦ ∑ i, fᵢ(xᵢ)`. -/
def separableObjective {n : ℕ} (f : Fin n → ℝ → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ ∑ i, f i (x i)

/-- A mixed-integer linear extended formulation for maximizing a function over a feasible set. -/
structure MixedIntegerLinearFormulation (n : ℕ) (P : Set (Fin n → ℝ))
    (objective : (Fin n → ℝ) → ℝ) where
  vars : ℕ
  constraints : ℕ
  xEmbedding : Fin n ↪ Fin vars
  integerVars : Finset (Fin vars)
  A : Matrix (Fin constraints) (Fin vars) ℝ
  b : Fin constraints → ℝ
  c : Fin vars → ℝ
  of_original :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ P →
      ∃ y : Fin vars → ℝ,
        (∀ j ∈ integerVars, ∃ z : ℤ, y j = (z : ℝ)) ∧
        (∀ i, y (xEmbedding i) = x i) ∧
        (∀ r, (A.mulVec y) r ≤ b r) ∧
        objective x = ∑ j, c j * y j
  to_original :
    ∀ ⦃y : Fin vars → ℝ⦄,
      (∀ j ∈ integerVars, ∃ z : ℤ, y j = (z : ℝ)) →
      (∀ r, (A.mulVec y) r ≤ b r) →
      (fun i ↦ y (xEmbedding i)) ∈ P ∧
        objective (fun i ↦ y (xEmbedding i)) = ∑ j, c j * y j

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the finite type of
coordinate-piece pairs. -/
private abbrev PiecewiseMILPPieceIndex {n : ℕ} (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :=
  Σ i, Fin (hf i).pieces

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the conceptual variable
blocks of the extended formulation. -/
private abbrev PiecewiseMILPVariable {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :=
  Fin n ⊕ (↥S ⊕ (PiecewiseMILPPieceIndex l u f hf ⊕ PiecewiseMILPPieceIndex l u f hf))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the finite families of
inequalities used by the formulation. -/
private inductive PiecewiseMILPRow {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) where
  | vertexNonneg (v : ↥S)
  | vertexSumUpper
  | vertexSumLower
  | vertexLinkUpper (i : Fin n)
  | vertexLinkLower (i : Fin n)
  | selectorNonneg (p : PiecewiseMILPPieceIndex l u f hf)
  | selectorUpper (p : PiecewiseMILPPieceIndex l u f hf)
  | selectorSumUpper (i : Fin n)
  | selectorSumLower (i : Fin n)
  | pieceLower (p : PiecewiseMILPPieceIndex l u f hf)
  | pieceUpper (p : PiecewiseMILPPieceIndex l u f hf)
  | pieceSumUpper (i : Fin n)
  | pieceSumLower (i : Fin n)
  deriving Fintype

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: enumerate the conceptual
variable blocks by a `Fin` type. -/
private noncomputable def piecewiseMILPVariableEquiv {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    PiecewiseMILPVariable S l u f hf ≃ Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) :=
  Fintype.equivFin _

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: enumerate the conceptual
constraint rows by a `Fin` type. -/
private noncomputable def piecewiseMILPRowEquiv {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    PiecewiseMILPRow S l u f hf ≃ Fin (Fintype.card (PiecewiseMILPRow S l u f hf)) :=
  Fintype.equivFin _

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: read the original-variable
block of an enumerated extended vector. -/
private noncomputable def piecewiseMILPOriginal {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) (i : Fin n) : ℝ :=
  y (piecewiseMILPVariableEquiv S l u f hf (Sum.inl i))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: read a convex-combination
weight from an enumerated extended vector. -/
private noncomputable def piecewiseMILPVertexWeight {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) (v : ↥S) : ℝ :=
  y (piecewiseMILPVariableEquiv S l u f hf (Sum.inr (Sum.inl v)))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: read a piece selector from
an enumerated extended vector. -/
private noncomputable def piecewiseMILPSelector {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ)
    (p : PiecewiseMILPPieceIndex l u f hf) : ℝ :=
  y (piecewiseMILPVariableEquiv S l u f hf (Sum.inr (Sum.inr (Sum.inl p))))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: read a disaggregated
piece value from an enumerated extended vector. -/
private noncomputable def piecewiseMILPPieceValue {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ)
    (p : PiecewiseMILPPieceIndex l u f hf) : ℝ :=
  y (piecewiseMILPVariableEquiv S l u f hf (Sum.inr (Sum.inr (Sum.inr p))))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the original-variable
indices embed injectively into the flattened variable type. -/
private lemma piecewiseMILPOriginalIndex_injective {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Function.Injective (fun i ↦ piecewiseMILPVariableEquiv S l u f hf (Sum.inl i)) := by
  -- The enumeration and the `Sum.inl` constructor are both injective.
  intro i j hij
  exact Sum.inl.inj ((piecewiseMILPVariableEquiv S l u f hf).injective hij)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the original-variable
embedding of the flattened formulation. -/
private noncomputable def piecewiseMILPOriginalEmbedding {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Fin n ↪ Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) :=
  ⟨fun i ↦ piecewiseMILPVariableEquiv S l u f hf (Sum.inl i),
    piecewiseMILPOriginalIndex_injective S l u f hf⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: selector indices embed
injectively into the flattened variable type. -/
private lemma piecewiseMILPSelectorIndex_injective {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Function.Injective (fun p ↦
      piecewiseMILPVariableEquiv S l u f hf (Sum.inr (Sum.inr (Sum.inl p)))) := by
  -- Peeling off the enumeration and the three sum constructors recovers the selector index.
  intro p q hpq
  exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj
    ((piecewiseMILPVariableEquiv S l u f hf).injective hpq)))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the selector embedding of
the flattened formulation. -/
private noncomputable def piecewiseMILPSelectorEmbedding {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    PiecewiseMILPPieceIndex l u f hf ↪
      Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) :=
  ⟨fun p ↦ piecewiseMILPVariableEquiv S l u f hf (Sum.inr (Sum.inr (Sum.inl p))),
    piecewiseMILPSelectorIndex_injective S l u f hf⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the semantic conditions
on convex weights, selectors, and disaggregated values. -/
private def piecewiseMILPWitness {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ) : Prop :=
  (∀ v, 0 ≤ lam v) ∧
  (∑ v, lam v) = 1 ∧
  (∀ i, x i = ∑ v, lam v * v.1 i) ∧
  (∀ p, 0 ≤ delta p ∧ delta p ≤ 1) ∧
  (∀ i, (∑ j, delta ⟨i, j⟩) = 1) ∧
  (∀ p, (hf p.1).lower p.2 * delta p ≤ q p ∧
    q p ≤ (hf p.1).upper p.2 * delta p) ∧
  (∀ i, x i = ∑ j, q ⟨i, j⟩)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the left side of each
conceptual inequality, evaluated on a flattened vector. -/
private noncomputable def piecewiseMILPRowValue {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    PiecewiseMILPRow S l u f hf → ℝ
  | .vertexNonneg v => -piecewiseMILPVertexWeight S l u f hf y v
  | .vertexSumUpper => ∑ v, piecewiseMILPVertexWeight S l u f hf y v
  | .vertexSumLower => -∑ v, piecewiseMILPVertexWeight S l u f hf y v
  | .vertexLinkUpper i => piecewiseMILPOriginal S l u f hf y i -
      ∑ v, piecewiseMILPVertexWeight S l u f hf y v * v.1 i
  | .vertexLinkLower i => (∑ v, piecewiseMILPVertexWeight S l u f hf y v * v.1 i) -
      piecewiseMILPOriginal S l u f hf y i
  | .selectorNonneg p => -piecewiseMILPSelector S l u f hf y p
  | .selectorUpper p => piecewiseMILPSelector S l u f hf y p
  | .selectorSumUpper i => ∑ j, piecewiseMILPSelector S l u f hf y ⟨i, j⟩
  | .selectorSumLower i => -∑ j, piecewiseMILPSelector S l u f hf y ⟨i, j⟩
  | .pieceLower p => (hf p.1).lower p.2 * piecewiseMILPSelector S l u f hf y p -
      piecewiseMILPPieceValue S l u f hf y p
  | .pieceUpper p => piecewiseMILPPieceValue S l u f hf y p -
      (hf p.1).upper p.2 * piecewiseMILPSelector S l u f hf y p
  | .pieceSumUpper i => piecewiseMILPOriginal S l u f hf y i -
      ∑ j, piecewiseMILPPieceValue S l u f hf y ⟨i, j⟩
  | .pieceSumLower i => (∑ j, piecewiseMILPPieceValue S l u f hf y ⟨i, j⟩) -
      piecewiseMILPOriginal S l u f hf y i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the right side of each
conceptual inequality. -/
private def piecewiseMILPRowRhs {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    PiecewiseMILPRow S l u f hf → ℝ
  | .vertexNonneg _ => 0
  | .vertexSumUpper => 1
  | .vertexSumLower => -1
  | .vertexLinkUpper _ => 0
  | .vertexLinkLower _ => 0
  | .selectorNonneg _ => 0
  | .selectorUpper _ => 1
  | .selectorSumUpper _ => 1
  | .selectorSumLower _ => -1
  | .pieceLower _ => 0
  | .pieceUpper _ => 0
  | .pieceSumUpper _ => 0
  | .pieceSumLower _ => 0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: every conceptual row is
additive in the flattened variable vector. -/
private lemma piecewiseMILPRowValue_add {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y z : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    piecewiseMILPRowValue S l u f hf (y + z) =
      piecewiseMILPRowValue S l u f hf y + piecewiseMILPRowValue S l u f hf z := by
  have horiginal (i : Fin n) :
      piecewiseMILPOriginal S l u f hf (y + z) i =
        piecewiseMILPOriginal S l u f hf y i + piecewiseMILPOriginal S l u f hf z i := by
    rfl
  have hweight (v : ↥S) :
      piecewiseMILPVertexWeight S l u f hf (y + z) v =
        piecewiseMILPVertexWeight S l u f hf y v +
          piecewiseMILPVertexWeight S l u f hf z v := by
    rfl
  have hselector (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPSelector S l u f hf (y + z) p =
        piecewiseMILPSelector S l u f hf y p + piecewiseMILPSelector S l u f hf z p := by
    rfl
  have hpiece (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPPieceValue S l u f hf (y + z) p =
        piecewiseMILPPieceValue S l u f hf y p + piecewiseMILPPieceValue S l u f hf z p := by
    rfl
  -- Expand one row at a time; finite sums and weighted summands distribute directly.
  funext r
  cases r <;>
    simp only [piecewiseMILPRowValue, horiginal, hweight, hselector, hpiece, add_mul,
      Finset.sum_add_distrib, Pi.add_apply] <;>
    ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: every conceptual row is
homogeneous in the flattened variable vector. -/
private lemma piecewiseMILPRowValue_smul {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) (a : ℝ)
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    piecewiseMILPRowValue S l u f hf (a • y) =
      a • piecewiseMILPRowValue S l u f hf y := by
  have horiginal (i : Fin n) :
      piecewiseMILPOriginal S l u f hf (a • y) i =
        a * piecewiseMILPOriginal S l u f hf y i := by
    rfl
  have hweight (v : ↥S) :
      piecewiseMILPVertexWeight S l u f hf (a • y) v =
        a * piecewiseMILPVertexWeight S l u f hf y v := by
    rfl
  have hselector (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPSelector S l u f hf (a • y) p =
        a * piecewiseMILPSelector S l u f hf y p := by
    rfl
  have hpvalue (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPPieceValue S l u f hf (a • y) p =
        a * piecewiseMILPPieceValue S l u f hf y p := by
    rfl
  -- First isolate weighted and unweighted sums under scalar multiplication.
  have hvertex (i : Fin n) :
      (∑ v, (a * piecewiseMILPVertexWeight S l u f hf y v) * v.1 i) =
        a * ∑ v, piecewiseMILPVertexWeight S l u f hf y v * v.1 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hweightSum :
      (∑ v, a * piecewiseMILPVertexWeight S l u f hf y v) =
        a * ∑ v, piecewiseMILPVertexWeight S l u f hf y v := by
    rw [Finset.mul_sum]
  have hselectorSum (i : Fin n) :
      (∑ j, a * piecewiseMILPSelector S l u f hf y ⟨i, j⟩) =
        a * ∑ j, piecewiseMILPSelector S l u f hf y ⟨i, j⟩ := by
    rw [Finset.mul_sum]
  have hpiece (i : Fin n) :
      (∑ j, a * piecewiseMILPPieceValue S l u f hf y ⟨i, j⟩) =
        a * ∑ j, piecewiseMILPPieceValue S l u f hf y ⟨i, j⟩ := by
    rw [Finset.mul_sum]
  -- Expand one row at a time and use the two normalized sum identities.
  funext r
  cases r <;>
    simp only [piecewiseMILPRowValue, horiginal, hweight, hselector, hpvalue,
      Pi.smul_apply, smul_eq_mul, hvertex, hweightSum, hselectorSum, hpiece] <;>
    ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the conceptual row family
as a single linear map, whose matrix is used in the formulation. -/
private noncomputable def piecewiseMILPRowLinearMap {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    (Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) →ₗ[ℝ]
      PiecewiseMILPRow S l u f hf → ℝ :=
  { toFun := piecewiseMILPRowValue S l u f hf
    map_add' := piecewiseMILPRowValue_add S l u f hf
    map_smul' := piecewiseMILPRowValue_smul S l u f hf }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: row evaluation remains
additive after enumerating the row type. -/
private lemma piecewiseMILPFlattenedRowValue_add {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y z : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    (fun r ↦ piecewiseMILPRowValue S l u f hf (y + z)
      ((piecewiseMILPRowEquiv S l u f hf).symm r)) =
    (fun r ↦ piecewiseMILPRowValue S l u f hf y
      ((piecewiseMILPRowEquiv S l u f hf).symm r)) +
    fun r ↦ piecewiseMILPRowValue S l u f hf z
      ((piecewiseMILPRowEquiv S l u f hf).symm r) := by
  -- Apply the conceptual additivity theorem before reindexing rows.
  funext r
  exact congrFun (piecewiseMILPRowValue_add S l u f hf y z)
    ((piecewiseMILPRowEquiv S l u f hf).symm r)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: row evaluation remains
homogeneous after enumerating the row type. -/
private lemma piecewiseMILPFlattenedRowValue_smul {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) (a : ℝ)
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    (fun r ↦ piecewiseMILPRowValue S l u f hf (a • y)
      ((piecewiseMILPRowEquiv S l u f hf).symm r)) =
    a • fun r ↦ piecewiseMILPRowValue S l u f hf y
      ((piecewiseMILPRowEquiv S l u f hf).symm r) := by
  -- Apply the conceptual homogeneity theorem before reindexing rows.
  funext r
  exact congrFun (piecewiseMILPRowValue_smul S l u f hf a y)
    ((piecewiseMILPRowEquiv S l u f hf).symm r)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the conceptual row map with
both domain and codomain indexed by `Fin`. -/
private noncomputable def piecewiseMILPFlattenedRowLinearMap {n : ℕ}
    (S : Finset (Fin n → ℝ)) (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    (Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) →ₗ[ℝ]
      Fin (Fintype.card (PiecewiseMILPRow S l u f hf)) → ℝ :=
  { toFun := fun y r ↦ piecewiseMILPRowValue S l u f hf y
      ((piecewiseMILPRowEquiv S l u f hf).symm r)
    map_add' := piecewiseMILPFlattenedRowValue_add S l u f hf
    map_smul' := piecewiseMILPFlattenedRowValue_smul S l u f hf }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the flattened matrix of the
conceptual row family. -/
private noncomputable def piecewiseMILPMatrix {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Matrix (Fin (Fintype.card (PiecewiseMILPRow S l u f hf)))
      (Fin (Fintype.card (PiecewiseMILPVariable S l u f hf))) ℝ :=
  LinearMap.toMatrix' (piecewiseMILPFlattenedRowLinearMap S l u f hf)

-- End quote '

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the flattened right-hand
side of the conceptual row family. -/
private noncomputable def piecewiseMILPRhs {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Fin (Fintype.card (PiecewiseMILPRow S l u f hf)) → ℝ :=
  fun r ↦ piecewiseMILPRowRhs S l u f hf ((piecewiseMILPRowEquiv S l u f hf).symm r)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the linear objective on
the selector and disaggregated-value blocks. -/
private noncomputable def piecewiseMILPObjectiveValue {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) : ℝ :=
  ∑ p, ((hf p.1).slope p.2 * piecewiseMILPPieceValue S l u f hf y p +
    (hf p.1).intercept p.2 * piecewiseMILPSelector S l u f hf y p)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the extended objective is
additive. -/
private lemma piecewiseMILPObjectiveValue_add {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y z : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    piecewiseMILPObjectiveValue S l u f hf (y + z) =
      piecewiseMILPObjectiveValue S l u f hf y +
        piecewiseMILPObjectiveValue S l u f hf z := by
  have hselector (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPSelector S l u f hf (y + z) p =
        piecewiseMILPSelector S l u f hf y p + piecewiseMILPSelector S l u f hf z p := by
    rfl
  have hpvalue (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPPieceValue S l u f hf (y + z) p =
        piecewiseMILPPieceValue S l u f hf y p + piecewiseMILPPieceValue S l u f hf z p := by
    rfl
  -- Combine the two objective sums and verify distributivity termwise.
  simp only [piecewiseMILPObjectiveValue]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [hselector, hpvalue]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the extended objective is
homogeneous. -/
private lemma piecewiseMILPObjectiveValue_smul {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) (a : ℝ)
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    piecewiseMILPObjectiveValue S l u f hf (a • y) =
      a • piecewiseMILPObjectiveValue S l u f hf y := by
  have hselector (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPSelector S l u f hf (a • y) p =
        a * piecewiseMILPSelector S l u f hf y p := by
    rfl
  have hpvalue (p : PiecewiseMILPPieceIndex l u f hf) :
      piecewiseMILPPieceValue S l u f hf (a • y) p =
        a * piecewiseMILPPieceValue S l u f hf y p := by
    rfl
  -- Pull the scalar outside the objective sum and verify homogeneity termwise.
  simp only [piecewiseMILPObjectiveValue, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hselector, hpvalue]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the extended objective as
a one-coordinate linear map. -/
private noncomputable def piecewiseMILPObjectiveLinearMap {n : ℕ}
    (S : Finset (Fin n → ℝ)) (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    (Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) →ₗ[ℝ] Unit → ℝ :=
  { toFun := fun y _ ↦ piecewiseMILPObjectiveValue S l u f hf y
    map_add' := fun y z ↦ funext fun _ ↦ piecewiseMILPObjectiveValue_add S l u f hf y z
    map_smul' := fun a y ↦ funext fun _ ↦ piecewiseMILPObjectiveValue_smul S l u f hf a y }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the coefficient vector of
the flattened linear objective. -/
private noncomputable def piecewiseMILPObjective {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ :=
  fun k ↦ LinearMap.toMatrix' (piecewiseMILPObjectiveLinearMap S l u f hf) () k

-- End quote '

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: multiplying by the encoded
matrix evaluates the corresponding conceptual row. -/
private lemma piecewiseMILPMatrix_mulVec {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ)
    (r : PiecewiseMILPRow S l u f hf) :
    (piecewiseMILPMatrix S l u f hf).mulVec y (piecewiseMILPRowEquiv S l u f hf r) =
      piecewiseMILPRowValue S l u f hf y r := by
  -- Use the computation rule for `toMatrix'`, then cancel the row enumeration.
  rw [piecewiseMILPMatrix, LinearMap.toMatrix'_mulVec]
  -- End quote '
  simp [piecewiseMILPFlattenedRowLinearMap]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the encoded inequalities
are exactly the semantic convex-weight and disjunctive-piece conditions. -/
private lemma separablePiecewiseMILP_constraints_iff {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    (∀ r, (piecewiseMILPMatrix S l u f hf).mulVec y r ≤ piecewiseMILPRhs S l u f hf r) ↔
      piecewiseMILPWitness S l u f hf
        (piecewiseMILPOriginal S l u f hf y)
        (piecewiseMILPVertexWeight S l u f hf y)
        (piecewiseMILPSelector S l u f hf y)
        (piecewiseMILPPieceValue S l u f hf y) := by
  -- Pull a flattened row inequality back along the row enumeration.
  constructor
  · intro hrows
    have hrow (r : PiecewiseMILPRow S l u f hf) :
        piecewiseMILPRowValue S l u f hf y r ≤ piecewiseMILPRowRhs S l u f hf r := by
      rw [← piecewiseMILPMatrix_mulVec S l u f hf y r]
      simpa [piecewiseMILPRhs] using hrows (piecewiseMILPRowEquiv S l u f hf r)
    -- Each semantic equality is represented by its two opposite inequalities.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v
      simpa [piecewiseMILPRowValue, piecewiseMILPRowRhs] using
        hrow (.vertexNonneg v)
    · have hu := hrow .vertexSumUpper
      have hl := hrow .vertexSumLower
      simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs] at hu hl
      linarith
    · intro i
      have hu := hrow (.vertexLinkUpper i)
      have hl := hrow (.vertexLinkLower i)
      simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs] at hu hl
      linarith
    · intro p
      constructor
      · simpa [piecewiseMILPRowValue, piecewiseMILPRowRhs] using hrow (.selectorNonneg p)
      · simpa [piecewiseMILPRowValue, piecewiseMILPRowRhs] using hrow (.selectorUpper p)
    · intro i
      have hu := hrow (.selectorSumUpper i)
      have hl := hrow (.selectorSumLower i)
      simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs] at hu hl
      linarith
    · intro p
      constructor
      · have hp := hrow (.pieceLower p)
        simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs] at hp
        linarith
      · have hp := hrow (.pieceUpper p)
        simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs] at hp
        linarith
    · intro i
      have hu := hrow (.pieceSumUpper i)
      have hl := hrow (.pieceSumLower i)
      simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs] at hu hl
      linarith
  · intro hw r
    -- Push each semantic condition to its designated flattened row.
    have hrow (s : PiecewiseMILPRow S l u f hf) :
        piecewiseMILPRowValue S l u f hf y s ≤ piecewiseMILPRowRhs S l u f hf s := by
      rcases hw with ⟨hlam, hlamSum, hx, hdelta, hdeltaSum, hq, hqSum⟩
      cases s with
      | vertexNonneg v =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hlam v]
      | vertexSumUpper =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith
      | vertexSumLower =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith
      | vertexLinkUpper i =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hx i]
      | vertexLinkLower i =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hx i]
      | selectorNonneg p =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [(hdelta p).1]
      | selectorUpper p =>
          simpa only [piecewiseMILPRowValue, piecewiseMILPRowRhs] using (hdelta p).2
      | selectorSumUpper i =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hdeltaSum i]
      | selectorSumLower i =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hdeltaSum i]
      | pieceLower p =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [(hq p).1]
      | pieceUpper p =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [(hq p).2]
      | pieceSumUpper i =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hqSum i]
      | pieceSumLower i =>
          simp only [piecewiseMILPRowValue, piecewiseMILPRowRhs]
          linarith [hqSum i]
    have hm := piecewiseMILPMatrix_mulVec S l u f hf y
      ((piecewiseMILPRowEquiv S l u f hf).symm r)
    rw [Equiv.apply_symm_apply] at hm
    rw [hm]
    exact hrow ((piecewiseMILPRowEquiv S l u f hf).symm r)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the flattened coefficient
vector evaluates to the semantic extended objective. -/
private lemma separablePiecewiseMILP_objective_eq {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ) :
    (∑ k, piecewiseMILPObjective S l u f hf k * y k) =
      piecewiseMILPObjectiveValue S l u f hf y := by
  -- Read the unique output coordinate of the objective linear map's matrix equation.
  have h := congrFun
    (LinearMap.toMatrix'_mulVec (piecewiseMILPObjectiveLinearMap S l u f hf) y) ()
  -- End quote '
  simpa [piecewiseMILPObjective, Matrix.mulVec, dotProduct,
    piecewiseMILPObjectiveLinearMap] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: an integral real in the
unit interval is zero or one. -/
private lemma integralUnitInterval_eq_zero_or_one (a : ℝ) (haInt : ∃ z : ℤ, a = (z : ℝ))
    (ha : 0 ≤ a ∧ a ≤ 1) : a = 0 ∨ a = 1 := by
  -- Transfer the unit-interval bounds to the witnessing integer.
  obtain ⟨z, rfl⟩ := haInt
  have hz0 : 0 ≤ z := by
    exact_mod_cast ha.1
  have hz1 : z ≤ 1 := by
    exact_mod_cast ha.2
  have hz : z = 0 ∨ z = 1 := by
    omega
  rcases hz with rfl | rfl <;> norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: an integral unit-interval
family summing to one has a unique active coordinate. -/
private lemma integralUnitIntervalFamily_existsUniqueOne {α : Type*} [Fintype α]
    (delta : α → ℝ) (hInt : ∀ a, ∃ z : ℤ, delta a = (z : ℝ))
    (hBound : ∀ a, 0 ≤ delta a ∧ delta a ≤ 1) (hSum : ∑ a, delta a = 1) :
    ∃! a, delta a = 1 := by
  classical
  -- If no coordinate is one, integrality makes every coordinate zero, contradicting the sum.
  have hExists : ∃ a, delta a = 1 := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a, delta a = 0 := by
      intro a
      exact (integralUnitInterval_eq_zero_or_one (delta a) (hInt a) (hBound a)).resolve_right
        (hnone a)
    have hzeroSum : ∑ a, delta a = 0 := by
      simp [hzero]
    linarith
  obtain ⟨a, ha⟩ := hExists
  refine ⟨a, ha, ?_⟩
  intro b hb
  -- Removing the active coordinate leaves a nonnegative sum equal to zero.
  by_contra hba
  have hrest : ∑ x ∈ Finset.univ.erase a, delta x = 0 := by
    have hsplit := Finset.add_sum_erase Finset.univ delta (Finset.mem_univ a)
    rw [ha, hSum] at hsplit
    linarith
  have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩
  have hbzero : delta b = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ ↦ (hBound x).1)).mp hrest b hbmem
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: a one-hot disaggregated
interval representation evaluates the selected affine piece. -/
private lemma piecewiseCoordinateObjective_eq {a b : ℝ} {g : ℝ → ℝ}
    (hg : PiecewiseLinearOnInterval a b g)
    (x : ℝ) (delta q : Fin hg.pieces → ℝ)
    (hInt : ∀ j, ∃ z : ℤ, delta j = (z : ℝ))
    (hDelta : ∀ j, 0 ≤ delta j ∧ delta j ≤ 1)
    (hDeltaSum : ∑ j, delta j = 1)
    (hQ : ∀ j, hg.lower j * delta j ≤ q j ∧ q j ≤ hg.upper j * delta j)
    (hQSum : x = ∑ j, q j) :
    g x = ∑ j, (hg.slope j * q j + hg.intercept j * delta j) := by
  classical
  -- Select the unique integral unit-interval coordinate equal to one.
  obtain ⟨k, hk, hkUnique⟩ :=
    integralUnitIntervalFamily_existsUniqueOne delta hInt hDelta hDeltaSum
  have hdeltaZero (j : Fin hg.pieces) (hjk : j ≠ k) : delta j = 0 := by
    rcases integralUnitInterval_eq_zero_or_one (delta j) (hInt j) (hDelta j) with hj | hj
    · exact hj
    · exact False.elim (hjk (hkUnique j hj))
  have hqZero (j : Fin hg.pieces) (hjk : j ≠ k) : q j = 0 := by
    have hj := hQ j
    rw [hdeltaZero j hjk, mul_zero, mul_zero] at hj
    exact le_antisymm hj.2 hj.1
  -- All inactive disaggregated values vanish, so the active value equals `x`.
  have hxq : x = q k := by
    calc
      x = ∑ j, q j := hQSum
      _ = q k := Fintype.sum_eq_single k (fun j hjk ↦ hqZero j hjk)
  have hxInterval : x ∈ Set.Icc (hg.lower k) (hg.upper k) := by
    have hkBounds := hQ k
    rw [hk, mul_one, mul_one, ← hxq] at hkBounds
    exact hkBounds
  -- Evaluate the active affine piece and collapse the objective sum to that index.
  have hObjectiveSum :
      (∑ j, (hg.slope j * q j + hg.intercept j * delta j)) =
        hg.slope k * q k + hg.intercept k * delta k := by
    apply Fintype.sum_eq_single k
    intro j hjk
    rw [hqZero j hjk, hdeltaZero j hjk]
    ring
  calc
    g x = hg.slope k * x + hg.intercept k := hg.eq_affine k x hxInterval
    _ = hg.slope k * q k + hg.intercept k * delta k := by rw [hxq, hk, mul_one]
    _ = ∑ j, (hg.slope j * q j + hg.intercept j * delta j) := hObjectiveSum.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: pack semantic variables
into the flattened extended vector. -/
private noncomputable def piecewiseMILPEncode {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ) :
    Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ :=
  fun k ↦ match (piecewiseMILPVariableEquiv S l u f hf).symm k with
    | Sum.inl i => x i
    | Sum.inr (Sum.inl v) => lam v
    | Sum.inr (Sum.inr (Sum.inl p)) => delta p
    | Sum.inr (Sum.inr (Sum.inr p)) => q p

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: encoding preserves every
original coordinate. -/
private lemma piecewiseMILPEncode_original {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ) (i : Fin n) :
    piecewiseMILPOriginal S l u f hf (piecewiseMILPEncode S l u f hf x lam delta q) i = x i := by
  -- Cancel the variable enumeration at the original-variable constructor.
  simp [piecewiseMILPOriginal, piecewiseMILPEncode]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: encoding preserves every
convex-combination weight. -/
private lemma piecewiseMILPEncode_vertexWeight {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ) (v : ↥S) :
    piecewiseMILPVertexWeight S l u f hf (piecewiseMILPEncode S l u f hf x lam delta q) v =
      lam v := by
  -- Cancel the variable enumeration at the weight constructor.
  simp [piecewiseMILPVertexWeight, piecewiseMILPEncode]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: encoding preserves every
piece selector. -/
private lemma piecewiseMILPEncode_selector {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ)
    (p : PiecewiseMILPPieceIndex l u f hf) :
    piecewiseMILPSelector S l u f hf (piecewiseMILPEncode S l u f hf x lam delta q) p =
      delta p := by
  -- Cancel the variable enumeration at the selector constructor.
  simp [piecewiseMILPSelector, piecewiseMILPEncode]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: encoding preserves every
disaggregated piece value. -/
private lemma piecewiseMILPEncode_pieceValue {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ)
    (p : PiecewiseMILPPieceIndex l u f hf) :
    piecewiseMILPPieceValue S l u f hf (piecewiseMILPEncode S l u f hf x lam delta q) p =
      q p := by
  -- Cancel the variable enumeration at the disaggregated-value constructor.
  simp [piecewiseMILPPieceValue, piecewiseMILPEncode]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: membership in the convex
hull of a finset has barycentric weights indexed by its subtype. -/
private lemma memConvexHullFinset_existsWeights {n : ℕ} (S : Finset (Fin n → ℝ))
    {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ (S : Set (Fin n → ℝ))) :
    ∃ lam : ↥S → ℝ, (∀ v, 0 ≤ lam v) ∧ (∑ v, lam v) = 1 ∧
      (∑ v, lam v • (v.1 : Fin n → ℝ)) = x := by
  classical
  -- Restrict the ambient weight function supplied by `Finset.mem_convexHull'` to `↥S`.
  obtain ⟨w, hwNonneg, hwSum, hwCenter⟩ := (Finset.mem_convexHull').mp hx
  -- End quote '
  refine ⟨fun v ↦ w v.1, ?_, ?_, ?_⟩
  · intro v
    exact hwNonneg v.1 v.2
  · calc
      (∑ v : ↥S, w v.1) = ∑ v ∈ S.attach, w v.1 := by rw [Finset.univ_eq_attach]
      _ = ∑ v ∈ S, w v := Finset.sum_attach S w
      _ = 1 := hwSum
  · calc
      (∑ v : ↥S, w v.1 • (v.1 : Fin n → ℝ)) =
          ∑ v ∈ S.attach, w v.1 • (v.1 : Fin n → ℝ) := by rw [Finset.univ_eq_attach]
      _ = ∑ v ∈ S, w v • v := Finset.sum_attach S (fun v ↦ w v • v)
      _ = x := hwCenter

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: every point in the finite
convex hull and bounding box admits semantic extended variables with the correct objective. -/
private lemma exists_piecewiseMILPWitness {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    {x : Fin n → ℝ} (hxHull : x ∈ convexHull ℝ (S : Set (Fin n → ℝ)))
    (hxBox : x ∈ Set.Icc l u) :
    ∃ (lam : ↥S → ℝ) (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ),
      piecewiseMILPWitness S l u f hf x lam delta q ∧
      (∀ p, ∃ z : ℤ, delta p = (z : ℝ)) ∧
      separableObjective f x =
        ∑ p, ((hf p.1).slope p.2 * q p + (hf p.1).intercept p.2 * delta p) := by
  classical
  -- Obtain barycentric weights from finite-convex-hull membership.
  obtain ⟨lam, hLamNonneg, hLamSum, hLamCenter⟩ :=
    memConvexHullFinset_existsWeights S hxHull
  have hPiece : ∀ i, ∃ j, x i ∈ Set.Icc ((hf i).lower j) ((hf i).upper j) := by
    intro i
    have hi : x i ∈ Set.Icc (l i) (u i) := ⟨hxBox.1 i, hxBox.2 i⟩
    exact Set.mem_iUnion.mp ((hf i).cover hi)
  choose chosen hChosen using hPiece
  let delta : PiecewiseMILPPieceIndex l u f hf → ℝ :=
    fun p ↦ if p.2 = chosen p.1 then 1 else 0
  let q : PiecewiseMILPPieceIndex l u f hf → ℝ :=
    fun p ↦ if p.2 = chosen p.1 then x p.1 else 0
  -- Verify the semantic constraints block by block.
  have hWitness : piecewiseMILPWitness S l u f hf x lam delta q := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hLamNonneg
    · exact hLamSum
    · intro i
      have hi := congrFun hLamCenter i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi.symm
    · rintro ⟨i, j⟩
      by_cases hj : j = chosen i
      · simp [delta, hj]
      · simp [delta, hj]
    · intro i
      simp [delta]
    · rintro ⟨i, j⟩
      by_cases hj : j = chosen i
      · subst j
        simpa [delta, q] using hChosen i
      · simp [delta, q, hj]
    · intro i
      simp [q]
  have hIntegral : ∀ p, ∃ z : ℤ, delta p = (z : ℝ) := by
    intro p
    by_cases hp : p.2 = chosen p.1
    · exact ⟨1, by simp [delta, hp]⟩
    · exact ⟨0, by simp [delta, hp]⟩
  -- Apply the one-coordinate soundness lemma and sum it over all coordinates.
  have hObjective : separableObjective f x =
      ∑ p, ((hf p.1).slope p.2 * q p + (hf p.1).intercept p.2 * delta p) := by
    rw [separableObjective, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact piecewiseCoordinateObjective_eq (hf i) (x i)
      (fun j ↦ delta ⟨i, j⟩) (fun j ↦ q ⟨i, j⟩)
      (fun j ↦ hIntegral ⟨i, j⟩) (fun j ↦ hWitness.2.2.2.1 ⟨i, j⟩)
      (hWitness.2.2.2.2.1 i) (fun j ↦ hWitness.2.2.2.2.2.1 ⟨i, j⟩)
      (hWitness.2.2.2.2.2.2 i)
  exact ⟨lam, delta, q, hWitness, hIntegral, hObjective⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: every integral semantic
witness projects to the finite convex hull and has the stated objective value. -/
private lemma piecewiseMILPWitness_sound {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (x : Fin n → ℝ) (lam : ↥S → ℝ)
    (delta q : PiecewiseMILPPieceIndex l u f hf → ℝ)
    (hw : piecewiseMILPWitness S l u f hf x lam delta q)
    (hInt : ∀ p, ∃ z : ℤ, delta p = (z : ℝ)) :
    x ∈ convexHull ℝ (S : Set (Fin n → ℝ)) ∧
      separableObjective f x =
        ∑ p, ((hf p.1).slope p.2 * q p + (hf p.1).intercept p.2 * delta p) := by
  -- The weight block is directly a finite convex-combination certificate.
  have hxHull : x ∈ convexHull ℝ (S : Set (Fin n → ℝ)) := by
    refine mem_convexHull_of_exists_fintype lam (fun v : ↥S ↦ v.1) hw.1 hw.2.1 ?_ ?_
    · intro v
      exact v.2
    · funext i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (hw.2.2.1 i).symm
  -- The one-hot lemma evaluates each coordinate objective; sum the resulting identities.
  have hObjective : separableObjective f x =
      ∑ p, ((hf p.1).slope p.2 * q p + (hf p.1).intercept p.2 * delta p) := by
    rw [separableObjective, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    exact piecewiseCoordinateObjective_eq (hf i) (x i)
      (fun j ↦ delta ⟨i, j⟩) (fun j ↦ q ⟨i, j⟩)
      (fun j ↦ hInt ⟨i, j⟩) (fun j ↦ hw.2.2.2.1 ⟨i, j⟩)
      (hw.2.2.2.2.1 i) (fun j ↦ hw.2.2.2.2.2.1 ⟨i, j⟩)
      (hw.2.2.2.2.2.2 i)
  exact ⟨hxHull, hObjective⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: precisely the selector
coordinates are declared integral. -/
private noncomputable def piecewiseMILPIntegerVars {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Finset (Fin (Fintype.card (PiecewiseMILPVariable S l u f hf))) :=
  Finset.univ.map (piecewiseMILPSelectorEmbedding S l u f hf)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: a semantic witness gives a
feasible flattened extension of every original point. -/
private lemma piecewiseMILPOfOriginal {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (hBox : convexHull ℝ (S : Set (Fin n → ℝ)) ⊆ Set.Icc l u) :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ convexHull ℝ (S : Set (Fin n → ℝ)) →
      ∃ y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ,
        (∀ j ∈ piecewiseMILPIntegerVars S l u f hf, ∃ z : ℤ, y j = (z : ℝ)) ∧
        (∀ i, y (piecewiseMILPOriginalEmbedding S l u f hf i) = x i) ∧
        (∀ r, (piecewiseMILPMatrix S l u f hf).mulVec y r ≤
          piecewiseMILPRhs S l u f hf r) ∧
        separableObjective f x = ∑ j, piecewiseMILPObjective S l u f hf j * y j := by
  intro x hx
  obtain ⟨lam, delta, q, hw, hInt, hObjective⟩ :=
    exists_piecewiseMILPWitness S l u f hf hx (hBox hx)
  let y := piecewiseMILPEncode S l u f hf x lam delta q
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · -- Every declared integer coordinate is the image of a selector.
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨p, _, rfl⟩
    obtain ⟨z, hz⟩ := hInt p
    refine ⟨z, ?_⟩
    have hEncoded := piecewiseMILPEncode_selector S l u f hf x lam delta q p
    simpa only [y, piecewiseMILPSelectorEmbedding, piecewiseMILPSelector] using
      hEncoded.trans hz
  · -- Encoding preserves the original block.
    intro i
    simpa [y, piecewiseMILPOriginalEmbedding, piecewiseMILPOriginal] using
      piecewiseMILPEncode_original S l u f hf x lam delta q i
  · -- Transfer the semantic witness through the matrix-interface theorem.
    apply (separablePiecewiseMILP_constraints_iff S l u f hf y).2
    have hxDecoded : piecewiseMILPOriginal S l u f hf y = x := by
      funext i
      exact piecewiseMILPEncode_original S l u f hf x lam delta q i
    have hlamDecoded : piecewiseMILPVertexWeight S l u f hf y = lam := by
      funext v
      exact piecewiseMILPEncode_vertexWeight S l u f hf x lam delta q v
    have hdeltaDecoded : piecewiseMILPSelector S l u f hf y = delta := by
      funext p
      exact piecewiseMILPEncode_selector S l u f hf x lam delta q p
    have hqDecoded : piecewiseMILPPieceValue S l u f hf y = q := by
      funext p
      exact piecewiseMILPEncode_pieceValue S l u f hf x lam delta q p
    rw [hxDecoded, hlamDecoded, hdeltaDecoded, hqDecoded]
    exact hw
  · -- Transfer the semantic objective through the objective-interface theorem.
    have hObjectiveEncoded : piecewiseMILPObjectiveValue S l u f hf y =
        ∑ p, ((hf p.1).slope p.2 * q p + (hf p.1).intercept p.2 * delta p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [piecewiseMILPEncode_selector S l u f hf x lam delta q p,
        piecewiseMILPEncode_pieceValue S l u f hf x lam delta q p]
    calc
      separableObjective f x =
          ∑ p, ((hf p.1).slope p.2 * q p + (hf p.1).intercept p.2 * delta p) := hObjective
      _ = piecewiseMILPObjectiveValue S l u f hf y := hObjectiveEncoded.symm
      _ = ∑ j, piecewiseMILPObjective S l u f hf j * y j :=
        (separablePiecewiseMILP_objective_eq S l u f hf y).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: every feasible integral
flattened vector projects to a valid original point with the same objective. -/
private lemma piecewiseMILPToOriginal {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    ∀ ⦃y : Fin (Fintype.card (PiecewiseMILPVariable S l u f hf)) → ℝ⦄,
      (∀ j ∈ piecewiseMILPIntegerVars S l u f hf, ∃ z : ℤ, y j = (z : ℝ)) →
      (∀ r, (piecewiseMILPMatrix S l u f hf).mulVec y r ≤
        piecewiseMILPRhs S l u f hf r) →
      (fun i ↦ y (piecewiseMILPOriginalEmbedding S l u f hf i)) ∈
          convexHull ℝ (S : Set (Fin n → ℝ)) ∧
        separableObjective f (fun i ↦ y (piecewiseMILPOriginalEmbedding S l u f hf i)) =
          ∑ j, piecewiseMILPObjective S l u f hf j * y j := by
  intro y hInt hRows
  -- Decode matrix feasibility into the semantic witness interface.
  have hw := (separablePiecewiseMILP_constraints_iff S l u f hf y).1 hRows
  have hSelectorInt : ∀ p, ∃ z : ℤ,
      piecewiseMILPSelector S l u f hf y p = (z : ℝ) := by
    intro p
    have hp : piecewiseMILPSelectorEmbedding S l u f hf p ∈
        piecewiseMILPIntegerVars S l u f hf := by
      exact Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩
    simpa [piecewiseMILPSelector, piecewiseMILPSelectorEmbedding] using
      hInt (piecewiseMILPSelectorEmbedding S l u f hf p) hp
  obtain ⟨hxHull, hObjective⟩ := piecewiseMILPWitness_sound S l u f hf
    (piecewiseMILPOriginal S l u f hf y)
    (piecewiseMILPVertexWeight S l u f hf y)
    (piecewiseMILPSelector S l u f hf y)
    (piecewiseMILPPieceValue S l u f hf y) hw hSelectorInt
  -- Rewrite the decoded original block and the flattened objective.
  constructor
  · simpa [piecewiseMILPOriginal, piecewiseMILPOriginalEmbedding] using hxHull
  · calc
      separableObjective f (fun i ↦ y (piecewiseMILPOriginalEmbedding S l u f hf i)) =
          separableObjective f (piecewiseMILPOriginal S l u f hf y) := by
            rfl
      _ = piecewiseMILPObjectiveValue S l u f hf y := hObjective
      _ = ∑ j, piecewiseMILPObjective S l u f hf j * y j :=
        (separablePiecewiseMILP_objective_eq S l u f hf y).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean`: the explicit finite MILP
obtained from convex weights and one-hot affine-piece selectors. -/
private noncomputable def piecewiseMILPFormulation {n : ℕ} (S : Finset (Fin n → ℝ))
    (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i))
    (hBox : convexHull ℝ (S : Set (Fin n → ℝ)) ⊆ Set.Icc l u) :
    MixedIntegerLinearFormulation n (convexHull ℝ (S : Set (Fin n → ℝ)))
      (separableObjective f) :=
  { vars := Fintype.card (PiecewiseMILPVariable S l u f hf)
    constraints := Fintype.card (PiecewiseMILPRow S l u f hf)
    xEmbedding := piecewiseMILPOriginalEmbedding S l u f hf
    integerVars := piecewiseMILPIntegerVars S l u f hf
    A := piecewiseMILPMatrix S l u f hf
    b := piecewiseMILPRhs S l u f hf
    c := piecewiseMILPObjective S l u f hf
    of_original := piecewiseMILPOfOriginal S l u f hf hBox
    to_original := piecewiseMILPToOriginal S l u f hf }

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_23.lean
Exercise 2.23: if `P ⊆ [l, u]` is a polytope and each coordinate objective `f i` is piecewise
linear on `[l i, u i]`, then maximizing `∑ i, f i (x i)` over `x ∈ P` admits a mixed-integer
linear programming formulation. -/
theorem separable_piecewise_linear_maximization_has_milp_formulation
    {n : ℕ} (P : Set (Fin n → ℝ)) (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hP_polytope : P.IsPolytope ℝ)
    (hP : P ⊆ Set.Icc l u)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Nonempty (MixedIntegerLinearFormulation n P (separableObjective f)) := by
  classical
  -- Replace the polytope by its finite vertex presentation.
  obtain ⟨V, hVFinite, rfl⟩ := hP_polytope
  let S : Finset (Fin n → ℝ) := hVFinite.toFinset
  have hBox : convexHull ℝ (S : Set (Fin n → ℝ)) ⊆ Set.Icc l u := by
    simpa [S, hVFinite.coe_toFinset] using hP
  -- Instantiate the explicit formulation and transport along `↑S = V`.
  have hForm : Nonempty
      (MixedIntegerLinearFormulation n (convexHull ℝ (S : Set (Fin n → ℝ)))
        (separableObjective f)) :=
    ⟨piecewiseMILPFormulation S l u f hf hBox⟩
  simpa [S, hVFinite.coe_toFinset] using hForm

#print axioms separable_piecewise_linear_maximization_has_milp_formulation
