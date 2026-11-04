/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_theorem_1_5
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped BigOperators Matrix

-- Chapter 6 keeps the tableau relaxation `P(B)` as the owner declaration here; later files reuse
-- it directly, while rational-tableau statements specialize it by coercing the tableau data to
-- `ℝ`. Polyhedron conclusions are bridged to the Chapter 3 canonical `Fin`-coordinate owner.

section Lemma62

variable {I N : Type}

section FinCoordinates

variable [Fintype I]

/-- Bridge/view: the canonical `Fin`-coordinate linear equivalence `ℝ^I ≃ ℝ^(Fin |I|)`. -/
noncomputable abbrev finCoordinateEquiv : (I → ℝ) ≃ₗ[ℝ] Fin (Fintype.card I) → ℝ :=
  LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin I).symm

/-- The canonical `Fin`-coordinate view of a subset of `ℝ^I`. This is the bridge to the Chapter 3
polyhedron owner on `Set (Fin n → ℝ)`. -/
noncomputable def finCoordinateSet (P : Set (I → ℝ)) : Set (Fin (Fintype.card I) → ℝ) :=
  finCoordinateEquiv '' P

/-- Membership in `finCoordinateSet P` means that the inverse reindexing of the point belongs to
the original set `P`. -/
@[simp] theorem mem_finCoordinateSet_iff
    (P : Set (I → ℝ))
    (x : Fin (Fintype.card I) → ℝ) :
    x ∈ finCoordinateSet P ↔ finCoordinateEquiv.symm x ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h :
        finCoordinateEquiv.symm (finCoordinateEquiv y) = y := by
      ext i
      simp [finCoordinateEquiv]
    exact h.symm ▸ hy
  · intro hx
    refine ⟨finCoordinateEquiv.symm x, hx, ?_⟩
    ext i
    simp [finCoordinateEquiv]

/-- A finite-indexed subset of `ℝ^I` is polyhedral in the Chapter 3 sense exactly when its
canonical `Fin`-coordinate view is cut out by finitely many linear inequalities. -/
theorem is_polyhedron_finCoordinateSet_iff
    (P : Set (I → ℝ)) :
    is_polyhedron (finCoordinateSet P) ↔
      ∃ m : ℕ,
        ∃ A : Matrix (Fin m) (Fin (Fintype.card I)) ℝ,
          ∃ b : Fin m → ℝ, finCoordinateSet P = polyhedron_le_set A b := by
  rw [is_polyhedron_iff]

/-- Helper for Lemma 6.2: reindexing a finite-coordinate polyhedron along a coordinate
equivalence just reindexes the matrix columns. -/
theorem funCongrLeft_image_polyhedron_le_set
    {n k m : ℕ}
    (e : Fin n ≃ Fin k)
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ) :
    (LinearEquiv.funCongrLeft ℝ ℝ e '' polyhedron_le_set A b) =
      polyhedron_le_set (fun i j ↦ A i (e j)) b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Reindex the coordinates in the defining inequalities once and keep the same rows.
    intro i
    have hrow :
        (((fun i j ↦ A i (e j)) *ᵥ (LinearEquiv.funCongrLeft ℝ ℝ e x)) i) =
          (A *ᵥ x) i := by
      have hsum :
          ∑ j : Fin n, A i (e j) * x (e j) = ∑ j : Fin k, A i j * x j := by
        simpa using Equiv.sum_comp e (fun j : Fin k ↦ A i j * x j)
      simpa [Matrix.mulVec, dotProduct, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
        using hsum
    exact hrow.symm ▸ hx i
  · intro hy
    refine ⟨(LinearEquiv.funCongrLeft ℝ ℝ e).symm y, ?_, ?_⟩
    · -- The inverse reindexing satisfies exactly the original row inequalities.
      intro i
      have hrow :
          ((A *ᵥ ((LinearEquiv.funCongrLeft ℝ ℝ e).symm y)) i) =
            (((fun i j ↦ A i (e j)) *ᵥ y) i) := by
        have hsum :
            ∑ j : Fin k, A i j * y (e.symm j) = ∑ j : Fin n, A i (e j) * y j := by
          simpa using (Equiv.sum_comp e (fun j : Fin k ↦ A i j * y (e.symm j))).symm
        simpa [Matrix.mulVec, dotProduct, LinearEquiv.funCongrLeft_symm,
          LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply] using hsum
      exact hrow ▸ hy i
    · ext j
      simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- Helper for Lemma 6.2: coordinate reindexing preserves polyhedrality. -/
theorem is_polyhedron_image_funCongrLeft
    {n k : ℕ}
    (e : Fin n ≃ Fin k)
    {P : Set (Fin k → ℝ)}
    (hP : is_polyhedron P) :
    is_polyhedron ((LinearEquiv.funCongrLeft ℝ ℝ e) '' P) := by
  rcases hP with ⟨m, A, b, rfl⟩
  -- Reuse the same finite row family after reindexing the coordinate columns.
  refine ⟨m, fun i j ↦ A i (e j), b, ?_⟩
  exact funCongrLeft_image_polyhedron_le_set e A b

end FinCoordinates

/-- The tableau-coordinate model of the mixed-integer set `ℤ^p × ℝ^(n - p)`, where the left
summand `I` is the integer block and the right summand `N` is the unrestricted real block. -/
def tableau_mixed_integer_lattice : Set (Sum I N → ℝ) :=
  {x | ∀ i : I, ∃ z : ℤ, x (Sum.inl i) = (z : ℝ)}

/-- Membership in `tableau_mixed_integer_lattice` means integrality of every coordinate in the
left summand `I`. -/
@[simp] theorem mem_tableau_mixed_integer_lattice_iff
    (x : Sum I N → ℝ) :
    x ∈ tableau_mixed_integer_lattice ↔
      ∀ i : I, ∃ z : ℤ, x (Sum.inl i) = (z : ℝ) :=
  Iff.rfl

/-- Helper for Lemma 6.2: the zero tableau vector belongs to the mixed-integer lattice. -/
theorem zero_mem_tableau_mixed_integer_lattice :
    (0 : Sum I N → ℝ) ∈ tableau_mixed_integer_lattice := by
  -- Every basic coordinate of the zero vector is the integer `0`.
  intro i
  refine ⟨0, ?_⟩
  simp

/-- Helper for Lemma 6.2: the tableau mixed-integer lattice is closed under addition. -/
theorem add_mem_tableau_mixed_integer_lattice
    {x y : Sum I N → ℝ}
    (hx : x ∈ tableau_mixed_integer_lattice)
    (hy : y ∈ tableau_mixed_integer_lattice) :
    x + y ∈ tableau_mixed_integer_lattice := by
  -- Add the integer basic coordinates coordinatewise.
  intro i
  rcases hx i with ⟨zx, hzx⟩
  rcases hy i with ⟨zy, hzy⟩
  refine ⟨zx + zy, ?_⟩
  simp [hzx, hzy]

/-- Helper for Lemma 6.2: the tableau mixed-integer lattice is closed under integer scaling. -/
theorem intCast_smul_mem_tableau_mixed_integer_lattice
    {x : Sum I N → ℝ}
    (z : ℤ)
    (hx : x ∈ tableau_mixed_integer_lattice) :
    (z : ℝ) • x ∈ tableau_mixed_integer_lattice := by
  -- Scaling an integer basic coordinate by an integer stays integral.
  intro i
  rcases hx i with ⟨w, hw⟩
  refine ⟨z * w, ?_⟩
  simp [hw, smul_eq_mul]

/-- Helper for Lemma 6.2: finite sums of tableau mixed-integer lattice vectors stay in the
tableau mixed-integer lattice. -/
theorem sum_mem_tableau_mixed_integer_lattice
    {α : Type} (s : Finset α) (v : α → Sum I N → ℝ)
    (hv : ∀ a ∈ s, v a ∈ tableau_mixed_integer_lattice) :
    Finset.sum s v ∈ tableau_mixed_integer_lattice := by
  -- Induct over the finite sum and use additivity of the lattice condition.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using zero_mem_tableau_mixed_integer_lattice (I := I) (N := N)
  | @insert a s ha ih =>
      have ha_mem : v a ∈ tableau_mixed_integer_lattice := hv a (by simp [ha])
      have hs_mem : Finset.sum s v ∈ tableau_mixed_integer_lattice := by
        refine ih ?_
        intro b hb
        exact hv b (by simp [hb])
      simpa [Finset.sum_insert, ha] using
        add_mem_tableau_mixed_integer_lattice (I := I) (N := N) ha_mem hs_mem

/-- Helper for Lemma 6.2: a single-coordinate selector row evaluates to the chosen coordinate
times the selector scalar. -/
@[simp] theorem sumSelectorMul_eq
    {n : ℕ}
    (i : Fin n)
    (c : ℚ)
    (x : Fin n → ℝ) :
    (∑ j : Fin n, (((if i = j then c else 0 : ℚ) : ℝ) * x j)) = (c : ℝ) * x i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hij : i ≠ j := fun h => hj h.symm
    simp [hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

section Tableau

variable [Fintype N]

/-- Helper for Lemma 6.2: the split `Fin`-coordinate order on tableau coordinates first lists the
basic block and then the nonbasic block. -/
noncomputable def tableauCoordinateEquiv [Fintype I] :
    Fin (Fintype.card I + Fintype.card N) ≃ Sum I N :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Fintype.equivFin I).symm (Fintype.equivFin N).symm)

/-- Helper for Lemma 6.2: the Chapter 4 mixed-space view of tableau coordinates. -/
noncomputable def tableauToMixedPointEquiv [Fintype I] :
    (Sum I N → ℝ) ≃ₗ[ℝ] MixedRealPoint (Fintype.card I) (Fintype.card N) where
  toFun x :=
    (fun i ↦ x (Sum.inl ((Fintype.equivFin I).symm i)),
      fun j ↦ x (Sum.inr ((Fintype.equivFin N).symm j)))
  invFun xy :=
    Sum.elim
      (fun i ↦ xy.1 (Fintype.equivFin I i))
      (fun j ↦ xy.2 (Fintype.equivFin N j))
  left_inv := by
    intro x
    ext z
    cases z with
    | inl i => simp
    | inr j => simp
  right_inv := by
    intro xy
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;> simp

/-- Helper for Lemma 6.2: flattening the mixed-space tableau image gives the split `Fin`-ordered
tableau coordinates. -/
theorem appendEquiv_tableauToMixedPointEquiv_eq_tableauFlatEquiv
    [Fintype I]
    (x : Sum I N → ℝ) :
    Fin.appendEquiv (Fintype.card I) (Fintype.card N) (tableauToMixedPointEquiv x) =
      (LinearEquiv.funCongrLeft ℝ ℝ (tableauCoordinateEquiv (I := I) (N := N))) x := by
  ext t
  refine Fin.addCases ?_ ?_ t
  · intro i
    -- On the left block, both coordinate views read the same basic tableau coordinate.
    simp [tableauToMixedPointEquiv, tableauCoordinateEquiv, LinearEquiv.funCongrLeft,
      finSumFinEquiv_symm_apply_castAdd]
  · intro j
    -- On the right block, both coordinate views read the same nonbasic tableau coordinate.
    simp [tableauToMixedPointEquiv, tableauCoordinateEquiv, LinearEquiv.funCongrLeft,
      finSumFinEquiv_symm_apply_natAdd]

/-- The tableau relaxation `P(B)`: the basic coordinates satisfy the tableau equations and the
nonbasic coordinates are nonnegative. -/
def tableau_corner_relaxation
    (abar : I → N → ℝ)
    (bbar : I → ℝ) : Set (Sum I N → ℝ) :=
  {x |
    (∀ i : I,
      x (Sum.inl i) = bbar i - ∑ j : N, abar i j * x (Sum.inr j)) ∧
      ∀ j : N, 0 ≤ x (Sum.inr j)}

/-- Membership in `tableau_corner_relaxation abar bbar` is exactly the tableau equation system
for the left summand together with nonnegativity on the right summand. -/
@[simp] theorem mem_tableau_corner_relaxation_iff
    (abar : I → N → ℝ)
    (bbar : I → ℝ)
    (x : Sum I N → ℝ) :
    x ∈ tableau_corner_relaxation abar bbar ↔
      (∀ i : I,
        x (Sum.inl i) = bbar i - ∑ j : N, abar i j * x (Sum.inr j)) ∧
        ∀ j : N, 0 ≤ x (Sum.inr j) :=
  Iff.rfl

/-- The rational specialization of `tableau_corner_relaxation`, obtained by coercing the tableau
data to `ℝ`. This is the source-facing rational bridge to the real tableau owner
`tableau_corner_relaxation`. -/
abbrev rationalTableauCornerRelaxation
    (abar : I → N → ℚ)
    (bbar : I → ℚ) : Set (Sum I N → ℝ) :=
  tableau_corner_relaxation (fun i j ↦ (abar i j : ℝ)) (fun i ↦ (bbar i : ℝ))

/-- Membership in `rationalTableauCornerRelaxation abar bbar` is exactly the real tableau system
attached to the rational data `abar`, `bbar`. -/
@[simp] theorem mem_rationalTableauCornerRelaxation_iff
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (x : Sum I N → ℝ) :
    x ∈ rationalTableauCornerRelaxation abar bbar ↔
      (∀ i : I,
        x (Sum.inl i) = (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j)) ∧
        ∀ j : N, 0 ≤ x (Sum.inr j) :=
  Iff.rfl

/-- The affine hull of the rational tableau relaxation contains a mixed-integer lattice point. -/
def tableauAffineSpanHasMixedIntegerPoint
    (abar : I → N → ℚ)
    (bbar : I → ℚ) : Prop :=
  ∃ x : Sum I N → ℝ,
    x ∈ affineSpan ℝ (rationalTableauCornerRelaxation abar bbar) ∧
      x ∈ tableau_mixed_integer_lattice

/-- `tableauAffineSpanHasMixedIntegerPoint abar bbar` unfolds to the existence of a
mixed-integer lattice point in the affine hull of the rational tableau relaxation. -/
theorem tableauAffineSpanHasMixedIntegerPoint_iff
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    tableauAffineSpanHasMixedIntegerPoint abar bbar ↔
      ∃ x : Sum I N → ℝ,
        x ∈ affineSpan ℝ (rationalTableauCornerRelaxation abar bbar) ∧
          x ∈ tableau_mixed_integer_lattice :=
  Iff.rfl

/-- The source corner polyhedron `corner(B)`, namely the convex hull of the mixed-integer points
of the tableau polyhedron `P(B)`. -/
def gomory_corner_polyhedron
    (abar : I → N → ℚ)
    (bbar : I → ℚ) : Set (Sum I N → ℝ) :=
  convexHull ℝ
    (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice)

/-- `gomory_corner_polyhedron abar bbar` is, by definition, the convex hull of the mixed-integer
points of the rational specialization of `tableau_corner_relaxation`. -/
theorem gomory_corner_polyhedron_eq_convexHull
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    gomory_corner_polyhedron abar bbar =
      convexHull ℝ (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice) :=
  rfl

/-- Helper for Lemma 6.2: the tableau ray attached to the nonbasic index `j`. -/
noncomputable def tableauCornerRay
    (abar : I → N → ℚ)
    (j : N) : Sum I N → ℝ :=
  Sum.elim (fun i ↦ -(abar i j : ℝ)) <|
    let _ : DecidableEq N := Classical.decEq N
    Pi.single j (1 : ℝ)

omit [Fintype N] in
/-- Helper for Lemma 6.2: on a basic coordinate, `tableauCornerRay abar j` has value
`-(abar i j : ℝ)`. -/
@[simp] theorem tableauCornerRay_apply_inl
    (abar : I → N → ℚ)
    (j : N)
    (i : I) :
    tableauCornerRay abar j (Sum.inl i) = -(abar i j : ℝ) :=
  rfl

omit [Fintype N] in
/-- Helper for Lemma 6.2: on the distinguished nonbasic coordinate `j`, the tableau ray has
value `1`. -/
@[simp] theorem tableauCornerRay_apply_inr_self
    (abar : I → N → ℚ)
    (j : N) :
    tableauCornerRay abar j (Sum.inr j) = 1 := by
  classical
  simp [tableauCornerRay]

omit [Fintype N] in
/-- Helper for Lemma 6.2: on any other nonbasic coordinate, the tableau ray vanishes. -/
@[simp] theorem tableauCornerRay_apply_inr_of_ne
    (abar : I → N → ℚ)
    (j j' : N)
    (hj' : j' ≠ j) :
    tableauCornerRay abar j (Sum.inr j') = 0 := by
  classical
  simp [tableauCornerRay, hj']

omit [Fintype N] in
/-- Helper for Lemma 6.2: the tableau rays are linearly independent. -/
theorem tableauCornerRay_linearIndependent
    (abar : I → N → ℚ) :
    LinearIndependent ℝ (tableauCornerRay abar) := by
  classical
  -- Evaluate any finite dependence relation at the matching nonbasic coordinate.
  refine linearIndependent_iff'.2 ?_
  intro s g hg j hj
  have hsum :
      ∑ i ∈ s, g i * tableauCornerRay abar i (Sum.inr j) = 0 := by
    simpa [Finset.sum_apply, Pi.smul_apply] using
      congrArg (fun x : Sum I N → ℝ ↦ x (Sum.inr j)) hg
  have hsplit :
      g j * tableauCornerRay abar j (Sum.inr j) +
          ∑ i ∈ s.erase j, g i * tableauCornerRay abar i (Sum.inr j) = 0 := by
    simpa [Finset.sum_insert, hj] using hsum
  have htail :
      ∑ i ∈ s.erase j, g i * tableauCornerRay abar i (Sum.inr j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hij : i ≠ j := Finset.mem_erase.1 hi |>.1
    have hzero : tableauCornerRay abar i (Sum.inr j) = 0 :=
      tableauCornerRay_apply_inr_of_ne abar i j hij.symm
    simp [hzero]
  rw [htail, tableauCornerRay_apply_inr_self, mul_one, add_zero] at hsplit
  exact hsplit

/-- Helper for Lemma 6.2: the tableau apex with basic coordinates `b̄` and nonbasic coordinates
`0`. -/
def tableauCornerBasePoint
    (bbar : I → ℚ) : Sum I N → ℝ :=
  Sum.elim (fun i ↦ (bbar i : ℝ)) (fun _ ↦ 0)

/-- Helper for Lemma 6.2: on a basic coordinate, a linear combination of tableau rays is the
negative tableau row applied to the coefficient vector. -/
theorem sum_smul_tableauCornerRay_apply_inl
    (abar : I → N → ℚ)
    (μ : N → ℝ)
    (i : I) :
    (∑ j : N, μ j • tableauCornerRay abar j) (Sum.inl i) =
      -∑ j : N, (abar i j : ℝ) * μ j := by
  -- Evaluate each ray on the basic coordinate and factor out the common minus sign.
  rw [Finset.sum_apply]
  calc
    ∑ j : N, (μ j • tableauCornerRay abar j) (Sum.inl i)
        = ∑ j : N, -((abar i j : ℝ) * μ j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    _ = -∑ j : N, (abar i j : ℝ) * μ j := by
          rw [← Finset.sum_neg_distrib]

/-- Helper for Lemma 6.2: on a nonbasic coordinate, a linear combination of tableau rays
recovers the corresponding coefficient. -/
theorem sum_smul_tableauCornerRay_apply_inr
    (abar : I → N → ℚ)
    (μ : N → ℝ)
    (j : N) :
    (∑ j' : N, μ j' • tableauCornerRay abar j') (Sum.inr j) = μ j := by
  classical
  -- The tableau rays are the standard basis on the nonbasic block.
  rw [Finset.sum_apply]
  have hterm :
      ∀ k : N, (μ k • tableauCornerRay abar k) (Sum.inr j) = if k = j then μ j else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp [tableauCornerRay, Pi.smul_apply, smul_eq_mul]
    · simp [tableauCornerRay, Pi.smul_apply, smul_eq_mul, hk]
  simp_rw [hterm]
  simp

/-- Helper for Lemma 6.2: the affine hull cut out by the tableau equations
`x_i = b̄_i - ∑ j, āᵢⱼ x_j` on the basic block. -/
def tableauAffineHull
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    AffineSubspace ℝ (Sum I N → ℝ) where
  carrier :=
    {x : Sum I N → ℝ |
      ∀ i : I,
        x (Sum.inl i) = (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j)}
  smul_vsub_vadd_mem := by
    intro c x₁ x₂ x₃ hx₁ hx₂ hx₃ i
    -- Expand the tableau equations on each basic coordinate and use linearity of the finite sum.
    have hx₁i := hx₁ i
    have hx₂i := hx₂ i
    have hx₃i := hx₃ i
    have hsum :
        ∑ j : N, (abar i j : ℝ) * ((c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inr j)) =
          c * (∑ j : N, (abar i j : ℝ) * x₁ (Sum.inr j) -
              ∑ j : N, (abar i j : ℝ) * x₂ (Sum.inr j)) +
            ∑ j : N, (abar i j : ℝ) * x₃ (Sum.inr j) := by
      have hcoord :
          ∀ j : N,
            ((c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inr j)) =
              c * (x₁ (Sum.inr j) - x₂ (Sum.inr j)) + x₃ (Sum.inr j) := by
        intro j
        simp [Pi.smul_apply, vsub_eq_sub, vadd_eq_add]
      have hmul₁ :
          ∑ j : N, (abar i j : ℝ) * (c * x₁ (Sum.inr j)) =
            c * ∑ j : N, (abar i j : ℝ) * x₁ (Sum.inr j) := by
        calc
          ∑ j : N, (abar i j : ℝ) * (c * x₁ (Sum.inr j))
              = ∑ j : N, c * ((abar i j : ℝ) * x₁ (Sum.inr j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
          _ = c * ∑ j : N, (abar i j : ℝ) * x₁ (Sum.inr j) := by
                rw [← Finset.mul_sum]
      have hmul₂ :
          ∑ j : N, (abar i j : ℝ) * (c * x₂ (Sum.inr j)) =
            c * ∑ j : N, (abar i j : ℝ) * x₂ (Sum.inr j) := by
        calc
          ∑ j : N, (abar i j : ℝ) * (c * x₂ (Sum.inr j))
              = ∑ j : N, c * ((abar i j : ℝ) * x₂ (Sum.inr j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
          _ = c * ∑ j : N, (abar i j : ℝ) * x₂ (Sum.inr j) := by
                rw [← Finset.mul_sum]
      calc
        ∑ j : N, (abar i j : ℝ) * ((c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inr j))
            = ∑ j : N,
                (abar i j : ℝ) * (c * (x₁ (Sum.inr j) - x₂ (Sum.inr j)) + x₃ (Sum.inr j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [hcoord]
        _ = ∑ j : N, (abar i j : ℝ) * (c * x₁ (Sum.inr j)) -
              ∑ j : N, (abar i j : ℝ) * (c * x₂ (Sum.inr j)) +
              ∑ j : N, (abar i j : ℝ) * x₃ (Sum.inr j) := by
                simp_rw [mul_add, mul_sub]
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = c * ∑ j : N, (abar i j : ℝ) * x₁ (Sum.inr j) -
              c * ∑ j : N, (abar i j : ℝ) * x₂ (Sum.inr j) +
              ∑ j : N, (abar i j : ℝ) * x₃ (Sum.inr j) := by
                rw [hmul₁, hmul₂]
        _ = c * (∑ j : N, (abar i j : ℝ) * x₁ (Sum.inr j) -
              ∑ j : N, (abar i j : ℝ) * x₂ (Sum.inr j)) +
              ∑ j : N, (abar i j : ℝ) * x₃ (Sum.inr j) := by
                ring
    rw [show (c • (x₁ -ᵥ x₂) +ᵥ x₃) (Sum.inl i) =
        c * (x₁ (Sum.inl i) - x₂ (Sum.inl i)) + x₃ (Sum.inl i) by
          simp [Pi.smul_apply, vsub_eq_sub, vadd_eq_add]]
    rw [hx₁i, hx₂i, hx₃i, hsum]
    ring

/-- Helper for Lemma 6.2: membership in `tableauAffineHull abar bbar` is exactly the tableau
equation system on the basic coordinates. -/
@[simp] theorem mem_tableauAffineHull_iff
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (x : Sum I N → ℝ) :
    x ∈ tableauAffineHull abar bbar ↔
      ∀ i : I,
        x (Sum.inl i) = (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j) :=
  Iff.rfl

/-- Helper for Lemma 6.2: every point of `P(B)` lies in the tableau affine hull. -/
theorem rationalTableauCornerRelaxation_subset_tableauAffineHull
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    rationalTableauCornerRelaxation abar bbar ⊆ tableauAffineHull abar bbar := by
  intro x hx
  simpa using ((mem_rationalTableauCornerRelaxation_iff abar bbar x).1 hx).1

/-- Helper for Lemma 6.2: a tableau-feasible point is exactly the apex plus a nonnegative
combination of the tableau rays. -/
theorem mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (x : Sum I N → ℝ) :
    x ∈ rationalTableauCornerRelaxation abar bbar ↔
      ∃ μ : N → ℝ, (∀ j : N, 0 ≤ μ j) ∧
        x = tableauCornerBasePoint bbar + ∑ j : N, μ j • tableauCornerRay abar j := by
  constructor
  · intro hx
    -- Use the nonbasic coordinates of `x` as the ray coefficients.
    refine ⟨fun j ↦ x (Sum.inr j), hx.2, ?_⟩
    ext z
    cases z with
    | inl i =>
        have hxi := hx.1 i
        have hrepr :
            (((tableauCornerBasePoint bbar + ∑ j : N, x (Sum.inr j) • tableauCornerRay abar j) :
              Sum I N → ℝ) (Sum.inl i)) =
              (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j) := by
          simp [tableauCornerBasePoint, sub_eq_add_neg, mul_comm]
        exact hxi.trans hrepr.symm
    | inr j =>
        simpa [tableauCornerBasePoint] using
          (sum_smul_tableauCornerRay_apply_inr (abar := abar)
            (μ := fun j ↦ x (Sum.inr j)) (j := j)).symm
  · rintro ⟨μ, hμ, rfl⟩
    -- The apex-plus-rays normal form directly gives the tableau equations and nonnegativity.
    have hnonbasic :
        ∀ j : N,
          (((tableauCornerBasePoint bbar + ∑ j' : N, μ j' • tableauCornerRay abar j') :
            Sum I N → ℝ) (Sum.inr j)) = μ j := by
      intro j
      simpa [tableauCornerBasePoint] using
        (sum_smul_tableauCornerRay_apply_inr (abar := abar) (μ := μ) (j := j))
    constructor
    · intro i
      have hbasic :
          (((tableauCornerBasePoint bbar + ∑ j : N, μ j • tableauCornerRay abar j) :
            Sum I N → ℝ) (Sum.inl i)) =
            (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * μ j := by
        simp [tableauCornerBasePoint, sub_eq_add_neg, mul_comm]
      simpa [hnonbasic] using hbasic
    · intro j
      simpa [hnonbasic j] using hμ j

/-- Helper for Lemma 6.2: points in the tableau affine hull are exactly arbitrary combinations of
the tableau rays based at the apex. -/
theorem mem_tableauAffineHull_iff_exists_rayCombination
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (x : Sum I N → ℝ) :
    x ∈ tableauAffineHull abar bbar ↔
      ∃ μ : N → ℝ, x = tableauCornerBasePoint bbar + ∑ j : N, μ j • tableauCornerRay abar j := by
  constructor
  · intro hx
    -- The nonbasic coordinates again provide the ray coefficients.
    refine ⟨fun j ↦ x (Sum.inr j), ?_⟩
    ext z
    cases z with
    | inl i =>
        have hxi := hx i
        have hrepr :
            (((tableauCornerBasePoint bbar + ∑ j : N, x (Sum.inr j) • tableauCornerRay abar j) :
              Sum I N → ℝ) (Sum.inl i)) =
              (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j) := by
          simp [tableauCornerBasePoint, sub_eq_add_neg, mul_comm]
        exact hxi.trans hrepr.symm
    | inr j =>
        simpa [tableauCornerBasePoint] using
          (sum_smul_tableauCornerRay_apply_inr (abar := abar)
            (μ := fun j ↦ x (Sum.inr j)) (j := j)).symm
  · rintro ⟨μ, rfl⟩
    -- The same coordinate computation shows that every apex-plus-rays point satisfies the
    -- defining affine equations.
    have hnonbasic :
        ∀ j : N,
          (((tableauCornerBasePoint bbar + ∑ j' : N, μ j' • tableauCornerRay abar j') :
            Sum I N → ℝ) (Sum.inr j)) = μ j := by
      intro j
      simpa [tableauCornerBasePoint] using
        (sum_smul_tableauCornerRay_apply_inr (abar := abar) (μ := μ) (j := j))
    intro i
    have hbasic :
        (((tableauCornerBasePoint bbar + ∑ j : N, μ j • tableauCornerRay abar j) :
          Sum I N → ℝ) (Sum.inl i)) =
          (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * μ j := by
      simp [tableauCornerBasePoint, sub_eq_add_neg, mul_comm]
    simpa [hnonbasic] using hbasic

/-- Helper for Lemma 6.2: the equation-defined affine hull is the affine subspace through the
tableau apex with direction spanned by the tableau rays. -/
theorem tableauAffineHull_eq_mk'_span_tableauCornerRay
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    tableauAffineHull abar bbar =
      AffineSubspace.mk' (tableauCornerBasePoint bbar)
        (Submodule.span ℝ (Set.range (tableauCornerRay abar))) := by
  ext x
  -- The two affine subspaces have the same apex-plus-rays membership description.
  rw [mem_tableauAffineHull_iff_exists_rayCombination]
  rw [AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨μ, hμ⟩
    -- Convert the direction witness back into an apex-plus-rays point representation.
    refine ⟨μ, ?_⟩
    rw [hμ]
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  · rintro ⟨μ, hμ⟩
    -- Subtracting the apex leaves exactly the ray combination.
    refine ⟨μ, ?_⟩
    have hμ' :
        (∑ j : N, μ j • tableauCornerRay abar j) + tableauCornerBasePoint bbar =
          (x - tableauCornerBasePoint bbar) + tableauCornerBasePoint bbar := by
      exact congrArg (fun t : Sum I N → ℝ ↦ t + tableauCornerBasePoint bbar) hμ
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hμ'.symm

/-- Helper for Lemma 6.2: the tableau apex itself belongs to `P(B)`. -/
theorem tableauCornerBasePoint_mem_rationalTableauCornerRelaxation
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    tableauCornerBasePoint bbar ∈ rationalTableauCornerRelaxation abar bbar := by
  -- The apex is the zero ray combination.
  refine (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar
      (tableauCornerBasePoint bbar)).2 ?_
  refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, ?_⟩
  simp [tableauCornerBasePoint]

/-- Helper for Lemma 6.2: the affine span of `P(B)` is exactly the tableau affine hull. -/
theorem affineSpan_rationalTableauCornerRelaxation_eq_tableauAffineHull
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    affineSpan ℝ (rationalTableauCornerRelaxation abar bbar) = tableauAffineHull abar bbar := by
  classical
  apply le_antisymm
  · -- The affine span is contained in every affine subspace containing the tableau relaxation.
    exact affineSpan_le.2
      (rationalTableauCornerRelaxation_subset_tableauAffineHull abar bbar)
  · intro x hx
    -- Every point of the tableau affine hull is the apex plus a ray combination, and each ray
    -- already lies in the direction of the affine span of the tableau relaxation.
    rcases (mem_tableauAffineHull_iff_exists_rayCombination abar bbar x).1 hx with ⟨μ, rfl⟩
    have hbase :
        tableauCornerBasePoint bbar ∈ affineSpan ℝ (rationalTableauCornerRelaxation abar bbar) :=
      subset_affineSpan ℝ _ (tableauCornerBasePoint_mem_rationalTableauCornerRelaxation abar bbar)
    have hray :
        ∀ j : N,
          tableauCornerRay abar j ∈
            (affineSpan ℝ (rationalTableauCornerRelaxation abar bbar)).direction := by
      intro j
      have hshift_mem :
          tableauCornerBasePoint bbar + tableauCornerRay abar j ∈
            rationalTableauCornerRelaxation abar bbar := by
        refine (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar
            (tableauCornerBasePoint bbar + tableauCornerRay abar j)).2 ?_
        refine ⟨Pi.single j 1, ?_, ?_⟩
        · intro k
          by_cases hk : k = j
          · subst hk
            simp
          · simp [Pi.single, hk]
        · simp
      have hshift :
          tableauCornerBasePoint bbar + tableauCornerRay abar j ∈
            affineSpan ℝ (rationalTableauCornerRelaxation abar bbar) :=
        subset_affineSpan ℝ _ hshift_mem
      have hdiff := AffineSubspace.vsub_mem_direction hshift hbase
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff
    have hsum :
        ∑ j : N, μ j • tableauCornerRay abar j ∈
          (affineSpan ℝ (rationalTableauCornerRelaxation abar bbar)).direction := by
      refine Submodule.sum_mem _ ?_
      intro j hj
      exact Submodule.smul_mem _ _ (hray j)
    simpa [add_comm] using AffineSubspace.vadd_mem_of_mem_direction hsum hbase

/-- Helper for Lemma 6.2: the affine hull of `P(B)` has dimension `|N|`. -/
theorem finrank_direction_affineSpan_rationalTableauCornerRelaxation_eq_card
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    Module.finrank ℝ (affineSpan ℝ (rationalTableauCornerRelaxation abar bbar)).direction =
      Fintype.card N := by
  -- Rewrite the affine hull to the translated span of the tableau rays and compute the finrank.
  calc
    Module.finrank ℝ (affineSpan ℝ (rationalTableauCornerRelaxation abar bbar)).direction
        = Module.finrank ℝ (tableauAffineHull abar bbar).direction := by
            rw [affineSpan_rationalTableauCornerRelaxation_eq_tableauAffineHull]
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range (tableauCornerRay abar))) := by
          rw [tableauAffineHull_eq_mk'_span_tableauCornerRay, AffineSubspace.direction_mk']
    _ = Fintype.card N := by
          simpa using finrank_span_eq_card (tableauCornerRay_linearIndependent abar)

/-- Helper for Lemma 6.2: every tableau ray is a recession direction of `P(B)`. -/
theorem tableauCornerRay_mem_recessionCone_rationalTableauCornerRelaxation
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (j : N) :
    tableauCornerRay abar j ∈ recessionCone (rationalTableauCornerRelaxation abar bbar) := by
  classical
  rw [mem_recessionCone_iff]
  intro x hx a ha
  rcases
      (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar x).1 hx with
    ⟨μ, hμ, rfl⟩
  -- Increase only the `j`-th nonbasic coefficient in the apex-plus-rays normal form.
  refine (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar _).2 ?_
  refine ⟨Function.update μ j (μ j + a), ?_, ?_⟩
  · intro k
    by_cases hk : k = j
    · subst hk
      simpa [Function.update] using add_nonneg (hμ k) ha
    · simp [Function.update, hk, hμ k]
  · have hupdate :
        ∑ k : N, Function.update μ j (μ j + a) k • tableauCornerRay abar k =
          ∑ k : N, μ k • tableauCornerRay abar k + a • tableauCornerRay abar j := by
      have hpointwise :
          (fun k : N ↦ Function.update μ j (μ j + a) k • tableauCornerRay abar k) =
            Function.update (fun k : N ↦ μ k • tableauCornerRay abar k) j
              ((μ j + a) • tableauCornerRay abar j) := by
        funext k
        by_cases hk : k = j
        · subst hk
          simp [Function.update]
        · simp [Function.update, hk]
      rw [hpointwise, Finset.sum_update_of_mem (s := Finset.univ) (by simp)]
      have hsplit :
          ((μ j + a) • tableauCornerRay abar j) +
              ∑ k ∈ Finset.univ \ ({j} : Finset N), μ k • tableauCornerRay abar k =
            ∑ k : N, μ k • tableauCornerRay abar k + a • tableauCornerRay abar j := by
        have hsumμ :
            ∑ k : N, μ k • tableauCornerRay abar k =
              μ j • tableauCornerRay abar j +
                ∑ k ∈ Finset.univ \ ({j} : Finset N), μ k • tableauCornerRay abar k := by
          rw [show Finset.univ \ ({j} : Finset N) = Finset.univ.erase j by
              ext k
              simp]
          simpa only [add_comm] using
            ((Finset.sum_erase_add
              (s := Finset.univ)
              (f := fun k : N ↦ μ k • tableauCornerRay abar k)
              (Finset.mem_univ j))).symm
        rw [add_smul]
        calc
          μ j • tableauCornerRay abar j + a • tableauCornerRay abar j +
              ∑ k ∈ Finset.univ \ ({j} : Finset N), μ k • tableauCornerRay abar k
              = μ j • tableauCornerRay abar j +
                  ∑ k ∈ Finset.univ \ ({j} : Finset N), μ k • tableauCornerRay abar k +
                  a • tableauCornerRay abar j := by
                    abel
          _ = ∑ k : N, μ k • tableauCornerRay abar k + a • tableauCornerRay abar j := by
                rw [← hsumμ]
      exact hsplit
    -- Repack the updated coefficient vector as the old feasible point translated by `a • ray_j`.
    rw [hupdate]
    abel

section FloorWitness

variable [Fintype I]

/-- Helper for Lemma 6.2: the `j`-th tableau column, reindexed along `equivFin`, so that the
common-denominator API from Remark 1.1 applies. -/
noncomputable def tableauColumn
    (abar : I → N → ℚ)
    (j : N) : Fin (Fintype.card I) → ℚ :=
  fun k ↦ abar ((Fintype.equivFin I).symm k) j

/-- Helper for Lemma 6.2: the common denominator of the `j`-th tableau column. -/
noncomputable def tableauColumnDenominator
    (abar : I → N → ℚ)
    (j : N) : ℕ :=
  rational_vector_common_denominator (tableauColumn abar j)

omit [Fintype N] in
/-- Helper for Lemma 6.2: every tableau column denominator is nonzero because all rational
denominators are positive. -/
theorem tableauColumnDenominator_ne_zero
    (abar : I → N → ℚ)
    (j : N) :
    tableauColumnDenominator abar j ≠ 0 := by
  -- The common denominator is an `lcm` of positive coordinate denominators.
  rw [tableauColumnDenominator, rational_vector_common_denominator]
  exact Finset.lcm_ne_zero_iff.2 <| by
    intro k hk
    exact Nat.ne_of_gt (Rat.den_pos (tableauColumn abar j k))

omit [Fintype N] in
/-- Helper for Lemma 6.2: the denominator-clearing integer vector records the real values
`D_j * ā_{ij}` on the basic block. -/
theorem tableauColumn_scaled_entry_eq_real
    (abar : I → N → ℚ)
    (j : N)
    (i : I) :
    (((common_denominator_scaled_vector (tableauColumn abar j) ((Fintype.equivFin I) i) : ℤ) : ℝ)) =
      (tableauColumnDenominator abar j : ℝ) * (abar i j : ℝ) := by
  -- Evaluate the common-denominator scaling formula at the reindexed coordinate `i`.
  have hq :
      ((common_denominator_scaled_vector (tableauColumn abar j) ((Fintype.equivFin I) i) : ℤ) : ℚ) =
        (tableauColumnDenominator abar j : ℚ) * abar i j := by
    have hscaled :=
      congrFun (common_denominator_scaled_vector_eq_smul (tableauColumn abar j))
        ((Fintype.equivFin I) i)
    simpa [tableauColumn, tableauColumnDenominator] using hscaled
  exact_mod_cast hq

omit [Fintype N] in
/-- Helper for Lemma 6.2: clearing the denominators in one tableau column makes the scaled tableau
ray mixed-integer on the basic block. -/
theorem tableauColumnDenominator_smul_tableauCornerRay_mem_tableau_mixed_integer_lattice
    (abar : I → N → ℚ)
    (j : N) :
    ((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j) ∈
      tableau_mixed_integer_lattice := by
  -- On each basic coordinate, the scaled ray becomes the negative of an explicit integer.
  intro i
  refine ⟨-common_denominator_scaled_vector (tableauColumn abar j) ((Fintype.equivFin I) i), ?_⟩
  calc
    (((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j) (Sum.inl i))
        = (tableauColumnDenominator abar j : ℝ) * (-(abar i j : ℝ)) := by
            simp [Pi.smul_apply, smul_eq_mul]
    _ = -((tableauColumnDenominator abar j : ℝ) * (abar i j : ℝ)) := by ring
    _ = -(((common_denominator_scaled_vector (tableauColumn abar j) ((Fintype.equivFin I) i) :
          ℤ) : ℝ)) := by
            rw [tableauColumn_scaled_entry_eq_real]
    _ = ((-common_denominator_scaled_vector (tableauColumn abar j) ((Fintype.equivFin I) i) : ℤ) :
          ℝ) := by
            simp

/-- Helper for Lemma 6.2: reducing coefficients by integer multiples of cleared rays separates the
original ray combination from its lattice correction term. -/
theorem reducedRayCombination_eq_add_clearedRayCombination
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : N → E)
    (μ : N → ℝ)
    (D : N → ℝ)
    (q : N → ℤ) :
    (∑ j : N, (μ j - (q j : ℝ) * D j) • r j) =
      ∑ j : N, μ j • r j + ∑ j : N, (-(q j : ℝ)) • (D j • r j) := by
  -- Normalize each coefficient once so the lattice correction is a separate finite sum.
  calc
    ∑ j : N, (μ j - (q j : ℝ) * D j) • r j
        = ∑ j : N, (μ j • r j + (-(q j : ℝ)) • (D j • r j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              (μ j - (q j : ℝ) * D j) • r j
                  = (μ j + (-(q j : ℝ)) * D j) • r j := by
                      congr 1
                      ring
              _ = μ j • r j + ((-(q j : ℝ)) * D j) • r j := by
                    rw [add_smul]
              _ = μ j • r j + (-(q j : ℝ)) • (D j • r j) := by
                    rw [← smul_smul]
    _ = ∑ j : N, μ j • r j + ∑ j : N, (-(q j : ℝ)) • (D j • r j) := by
          rw [Finset.sum_add_distrib]

omit [Fintype I] in
/-- Helper for Lemma 6.2: an affine-hull mixed-integer witness can be reduced modulo the tableau
column denominators to produce a feasible mixed-integer point of `P(B)`. -/
theorem
    exists_mixedIntegerPoint_mem_rationalTableauCornerRelaxation_of_affineSpanHasMixedIntegerPoint
    [Finite I]
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (h_affine : tableauAffineSpanHasMixedIntegerPoint abar bbar) :
    ∃ x : Sum I N → ℝ,
      x ∈ rationalTableauCornerRelaxation abar bbar ∧
        x ∈ tableau_mixed_integer_lattice := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  rcases h_affine with ⟨x, hx_aff, hx_lattice⟩
  have hx_hull : x ∈ tableauAffineHull abar bbar := by
    -- Rewrite the affine-span assumption to the explicit tableau affine hull.
    simpa [affineSpan_rationalTableauCornerRelaxation_eq_tableauAffineHull] using hx_aff
  rcases (mem_tableauAffineHull_iff_exists_rayCombination abar bbar x).1 hx_hull with ⟨μ, rfl⟩
  let q : N → ℤ := fun j ↦ ⌊μ j / (tableauColumnDenominator abar j : ℝ)⌋
  let μred : N → ℝ :=
    fun j ↦ μ j - (q j : ℝ) * (tableauColumnDenominator abar j : ℝ)
  refine ⟨tableauCornerBasePoint bbar + ∑ j : N, μred j • tableauCornerRay abar j, ?_, ?_⟩
  · -- The reduced coefficients stay nonnegative, so they define a feasible tableau point.
    refine
      (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar _).2 ?_
    refine ⟨μred, ?_, rfl⟩
    intro j
    have hDnat : 0 < tableauColumnDenominator abar j :=
      Nat.pos_of_ne_zero (tableauColumnDenominator_ne_zero abar j)
    have hDreal : 0 < (tableauColumnDenominator abar j : ℝ) := by
      exact_mod_cast hDnat
    simpa [μred, q] using Int.sub_floor_div_mul_nonneg (μ j) hDreal
  · -- The reduced point is the original lattice point plus an integer combination of cleared rays.
    have hcorrection :
        (∑ j : N, (-(q j : ℝ)) •
            (((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j))) ∈
          tableau_mixed_integer_lattice := by
      refine sum_mem_tableau_mixed_integer_lattice
        (s := Finset.univ)
        (v := fun j : N ↦ (-(q j : ℝ)) •
          (((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j))) ?_
      intro j hj
      simpa using
        intCast_smul_mem_tableau_mixed_integer_lattice
          (I := I) (N := N) (-q j)
          (tableauColumnDenominator_smul_tableauCornerRay_mem_tableau_mixed_integer_lattice
            (I := I) (N := N) abar j)
    have hrewrite :
        tableauCornerBasePoint bbar + ∑ j : N, μred j • tableauCornerRay abar j =
          (tableauCornerBasePoint bbar + ∑ j : N, μ j • tableauCornerRay abar j) +
            ∑ j : N, (-(q j : ℝ)) •
              (((tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j)) := by
      -- Route correction: isolate the finite-sum normalization once instead of rewriting each
      -- reduced coefficient inside the tableau proof.
      have hsum :=
        congrArg
          (fun y : Sum I N → ℝ ↦ tableauCornerBasePoint bbar + y)
          (reducedRayCombination_eq_add_clearedRayCombination
            (r := tableauCornerRay abar)
            (μ := μ)
            (D := fun j ↦ (tableauColumnDenominator abar j : ℝ))
            (q := q))
      simpa [μred, q, add_assoc, add_left_comm, add_comm] using hsum
    rw [hrewrite]
    exact add_mem_tableau_mixed_integer_lattice (I := I) (N := N) hx_lattice hcorrection

end FloorWitness

/-- Helper for Lemma 6.2: once one feasible mixed-integer tableau point is known, every tableau
ray lies in the affine direction of the corner hull. -/
theorem tableauCornerRay_mem_direction_affineSpan_gomory_corner_polyhedron
    [Finite I]
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    {x0 : Sum I N → ℝ}
    (hx0_relax : x0 ∈ rationalTableauCornerRelaxation abar bbar)
    (hx0_lattice : x0 ∈ tableau_mixed_integer_lattice)
    (j : N) :
    tableauCornerRay abar j ∈
      (affineSpan ℝ (gomory_corner_polyhedron abar bbar)).direction := by
  let _ : Fintype I := Fintype.ofFinite I
  -- Place the cleared ray between two generators of the corner hull, then divide by the
  -- nonzero denominator.
  have hx0_corner : x0 ∈ gomory_corner_polyhedron abar bbar := by
    rw [gomory_corner_polyhedron_eq_convexHull]
    exact subset_convexHull ℝ _ ⟨hx0_relax, hx0_lattice⟩
  have hD_nonneg :
      0 ≤ (tableauColumnDenominator abar j : ℝ) := by
    exact Nat.cast_nonneg _
  have hshift_relax :
      x0 + (tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j ∈
        rationalTableauCornerRelaxation abar bbar := by
    exact (mem_recessionCone_iff.mp
      (tableauCornerRay_mem_recessionCone_rationalTableauCornerRelaxation abar bbar j))
      hx0_relax _ hD_nonneg
  have hshift_lattice :
      x0 + (tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j ∈
        tableau_mixed_integer_lattice := by
    exact add_mem_tableau_mixed_integer_lattice (I := I) (N := N)
      hx0_lattice
      (tableauColumnDenominator_smul_tableauCornerRay_mem_tableau_mixed_integer_lattice
        (I := I) (N := N) abar j)
  have hshift_corner :
      x0 + (tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j ∈
        gomory_corner_polyhedron abar bbar := by
    rw [gomory_corner_polyhedron_eq_convexHull]
    exact subset_convexHull ℝ _ ⟨hshift_relax, hshift_lattice⟩
  have hx0_aff :
      x0 ∈ affineSpan ℝ (gomory_corner_polyhedron abar bbar) :=
    subset_affineSpan ℝ _ hx0_corner
  have hshift_aff :
      x0 + (tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j ∈
        affineSpan ℝ (gomory_corner_polyhedron abar bbar) :=
    subset_affineSpan ℝ _ hshift_corner
  have hscaled :
      (tableauColumnDenominator abar j : ℝ) • tableauCornerRay abar j ∈
        (affineSpan ℝ (gomory_corner_polyhedron abar bbar)).direction := by
    have hdiff := AffineSubspace.vsub_mem_direction hshift_aff hx0_aff
    simpa [vsub_eq_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hdiff
  have hD_ne_zero : (tableauColumnDenominator abar j : ℝ) ≠ 0 := by
    exact_mod_cast tableauColumnDenominator_ne_zero (I := I) (N := N) abar j
  -- Scale away the nonzero denominator to recover the original tableau ray.
  simpa [smul_smul, hD_ne_zero] using
    (Submodule.smul_mem
      ((affineSpan ℝ (gomory_corner_polyhedron abar bbar)).direction)
      ((tableauColumnDenominator abar j : ℝ)⁻¹)
      hscaled)

/-- Helper for Lemma 6.2: the transported tableau relaxation is an explicit rational mixed
polyhedron in the Chapter 4 mixed-space owner. -/
theorem tableauToMixedPoint_image_rationalTableauCornerRelaxation_eq_rationalMixedPolyhedron
    [Fintype I]
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    ∃ m : ℕ,
      ∃ A : Matrix (Fin m) (Fin (Fintype.card I)) ℚ,
          ∃ G : Matrix (Fin m) (Fin (Fintype.card N)) ℚ,
          ∃ b : Fin m → ℚ,
            tableauToMixedPointEquiv '' rationalTableauCornerRelaxation abar bbar =
              rational_mixed_polyhedron A G b := by
  let m := Fintype.card I + (Fintype.card I + Fintype.card N)
  let A : Matrix (Fin m) (Fin (Fintype.card I)) ℚ :=
    fun r c =>
      match finSumFinEquiv.symm r with
      | Sum.inl i => if i = c then 1 else 0
      | Sum.inr s =>
          match finSumFinEquiv.symm s with
          | Sum.inl i => if i = c then -1 else 0
          | Sum.inr _ => 0
  let G : Matrix (Fin m) (Fin (Fintype.card N)) ℚ :=
    fun r c =>
      match finSumFinEquiv.symm r with
      | Sum.inl i => abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm c)
      | Sum.inr s =>
          match finSumFinEquiv.symm s with
          | Sum.inl i => -abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm c)
          | Sum.inr j => if j = c then -1 else 0
  let b : Fin m → ℚ :=
    fun r =>
      match finSumFinEquiv.symm r with
      | Sum.inl i => bbar ((Fintype.equivFin I).symm i)
      | Sum.inr s =>
          match finSumFinEquiv.symm s with
          | Sum.inl i => -bbar ((Fintype.equivFin I).symm i)
          | Sum.inr _ => 0
  refine ⟨m, A, G, b, ?_⟩
  ext xy
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rationalTableauCornerRelaxation_iff] at hx
    rw [mem_rational_mixed_polyhedron_iff]
    intro r
    rcases hrow : finSumFinEquiv.symm r with i | s
    · have hi := hx.1 ((Fintype.equivFin I).symm i)
      have hsum :
          ∑ j : Fin (Fintype.card N),
              ↑(abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j)) *
                x (Sum.inr ((Fintype.equivFin N).symm j)) =
            ∑ j : N, (abar ((Fintype.equivFin I).symm i) j : ℝ) * x (Sum.inr j) := by
        simpa using
          (Equiv.sum_comp (Fintype.equivFin N)
            (fun j : Fin (Fintype.card N) ↦
              (abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j) : ℝ) *
                x (Sum.inr ((Fintype.equivFin N).symm j)))).symm
      have hiLe :
          x (Sum.inl ((Fintype.equivFin I).symm i)) +
              ∑ j : Fin (Fintype.card N),
                ↑(abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j)) *
                  x (Sum.inr ((Fintype.equivFin N).symm j)) ≤
            (bbar ((Fintype.equivFin I).symm i) : ℝ) := by
        rw [hsum]
        linarith
      simpa [A, G, b, hrow, Matrix.mulVec, dotProduct, tableauToMixedPointEquiv,
        sumSelectorMul_eq] using hiLe
    · rcases hs : finSumFinEquiv.symm s with i | j
      · have hi := hx.1 ((Fintype.equivFin I).symm i)
        have hsum :
            ∑ j' : Fin (Fintype.card N),
                ↑(abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j')) *
                  x (Sum.inr ((Fintype.equivFin N).symm j')) =
              ∑ j' : N, (abar ((Fintype.equivFin I).symm i) j' : ℝ) * x (Sum.inr j') := by
          simpa using
            (Equiv.sum_comp (Fintype.equivFin N)
              (fun j' : Fin (Fintype.card N) ↦
                (abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j') : ℝ) *
                  x (Sum.inr ((Fintype.equivFin N).symm j')))).symm
        have hiEq :
            x (Sum.inl ((Fintype.equivFin I).symm i)) +
                ∑ j' : Fin (Fintype.card N),
                  ↑(abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j')) *
                    x (Sum.inr ((Fintype.equivFin N).symm j')) =
              (bbar ((Fintype.equivFin I).symm i) : ℝ) := by
          rw [hsum]
          linarith
        have hiLe :
            (bbar ((Fintype.equivFin I).symm i) : ℝ) +
                (-1 : ℝ) * x (Sum.inl ((Fintype.equivFin I).symm i)) ≤
              ∑ j' : Fin (Fintype.card N),
                ↑(abar ((Fintype.equivFin I).symm i) ((Fintype.equivFin N).symm j')) *
                  x (Sum.inr ((Fintype.equivFin N).symm j')) := by
          linarith
        simpa [A, G, b, hrow, hs, Matrix.mulVec, dotProduct, tableauToMixedPointEquiv,
          Rat.cast_neg,
          sumSelectorMul_eq] using hiLe
      · have hjLe : -x (Sum.inr ((Fintype.equivFin N).symm j)) ≤ (0 : ℝ) := by
          simpa using neg_nonpos.mpr (hx.2 ((Fintype.equivFin N).symm j))
        simpa [A, G, b, hrow, hs, Matrix.mulVec, dotProduct, tableauToMixedPointEquiv,
          Rat.cast_neg,
          sumSelectorMul_eq] using hjLe
  · intro hxy
    have hxy_eq :
        tableauToMixedPointEquiv ((tableauToMixedPointEquiv (I := I) (N := N)).symm xy) = xy :=
      (tableauToMixedPointEquiv (I := I) (N := N)).apply_symm_apply xy
    refine ⟨(tableauToMixedPointEquiv (I := I) (N := N)).symm xy, ?_, hxy_eq⟩
    rw [mem_rational_mixed_polyhedron_iff] at hxy
    rw [mem_rationalTableauCornerRelaxation_iff]
    constructor
    · intro i
      let iFin : Fin (Fintype.card I) := Fintype.equivFin I i
      have hi₁ :
          xy.1 iFin +
              ∑ j : Fin (Fintype.card N), ↑(abar i ((Fintype.equivFin N).symm j)) * xy.2 j ≤
            (bbar i : ℝ) := by
        simpa [A, G, b, Matrix.mulVec, dotProduct, iFin, sumSelectorMul_eq] using
          hxy (Fin.castAdd (Fintype.card I + Fintype.card N) iFin)
      have hi₂ :
          (bbar i : ℝ) ≤
            ∑ j : Fin (Fintype.card N), ↑(abar i ((Fintype.equivFin N).symm j)) * xy.2 j +
              xy.1 iFin := by
        have hi₂' :
            (bbar i : ℝ) + (-1 : ℝ) * xy.1 iFin ≤
              ∑ j : Fin (Fintype.card N), ↑(abar i ((Fintype.equivFin N).symm j)) * xy.2 j := by
          simpa [A, G, b, Matrix.mulVec, dotProduct, iFin, Rat.cast_neg,
            sumSelectorMul_eq,
            finSumFinEquiv_symm_apply_natAdd, Fin.castAdd_natAdd] using
            hxy (Fin.natAdd (Fintype.card I) (Fin.castAdd (Fintype.card N) iFin))
        linarith
      have heq :
          xy.1 iFin +
              ∑ j : Fin (Fintype.card N), ↑(abar i ((Fintype.equivFin N).symm j)) * xy.2 j =
            (bbar i : ℝ) := by
        linarith
      have hsum :
          ∑ j : Fin (Fintype.card N), ↑(abar i ((Fintype.equivFin N).symm j)) * xy.2 j =
            ∑ j : N, (abar i j : ℝ) *
              ((tableauToMixedPointEquiv (I := I) (N := N)).symm xy) (Sum.inr j) := by
        simpa [tableauToMixedPointEquiv] using
          (Equiv.sum_comp (Fintype.equivFin N)
            (fun j : Fin (Fintype.card N) ↦
              (abar i ((Fintype.equivFin N).symm j) : ℝ) * xy.2 j)).symm
      have hcoord :
          xy.1 iFin =
            (bbar i : ℝ) -
              ∑ j : Fin (Fintype.card N), ↑(abar i ((Fintype.equivFin N).symm j)) * xy.2 j := by
        linarith [heq]
      change ((tableauToMixedPointEquiv (I := I) (N := N)).symm xy) (Sum.inl i) =
        (bbar i : ℝ) -
          ∑ j : N, (abar i j : ℝ) *
            ((tableauToMixedPointEquiv (I := I) (N := N)).symm xy) (Sum.inr j)
      simpa [tableauToMixedPointEquiv, hsum] using hcoord
    · intro j
      let jFin : Fin (Fintype.card N) := Fintype.equivFin N j
      have hjLe : (-1 : ℝ) * xy.2 jFin ≤ (0 : ℝ) := by
        simpa [A, G, b, Matrix.mulVec, dotProduct, jFin, Rat.cast_neg,
          sumSelectorMul_eq,
          finSumFinEquiv_symm_apply_natAdd, Fin.castAdd_natAdd] using
          hxy (Fin.natAdd (Fintype.card I) (Fin.natAdd (Fintype.card I) jFin))
      have hjNeg : -xy.2 jFin ≤ (0 : ℝ) := by
        simpa using hjLe
      change 0 ≤ ((tableauToMixedPointEquiv (I := I) (N := N)).symm xy) (Sum.inr j)
      simpa [tableauToMixedPointEquiv] using neg_nonpos.mp hjNeg

/-- Helper for Lemma 6.2: the tableau mixed-integer lattice becomes the Chapter 4 mixed lattice
after transporting the coordinate owner. -/
theorem tableauToMixedPoint_image_tableauMixedIntegerLattice_eq_mixed_integer_lattice
    [Fintype I] :
    tableauToMixedPointEquiv '' tableau_mixed_integer_lattice =
      mixed_integer_lattice (Fintype.card I) (Fintype.card N) := by
  ext xy
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff]
    classical
    refine ⟨fun i ↦ Classical.choose (hx ((Fintype.equivFin I).symm i)), ?_⟩
    ext i
    exact Classical.choose_spec (hx ((Fintype.equivFin I).symm i))
  · intro hxy
    rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff] at hxy
    have hxy_eq :
        tableauToMixedPointEquiv (tableauToMixedPointEquiv.symm xy) = xy :=
      (tableauToMixedPointEquiv (I := I) (N := N)).apply_symm_apply xy
    refine ⟨tableauToMixedPointEquiv.symm xy, ?_, hxy_eq⟩
    rcases hxy with ⟨z, hz⟩
    intro i
    refine ⟨z (Fintype.equivFin I i), ?_⟩
    simpa [tableauToMixedPointEquiv] using congrFun hz (Fintype.equivFin I i)

/-- Helper for Lemma 6.2: transporting the corner hull aligns it with the mixed-integer hull of
the transported tableau relaxation. -/
theorem image_gomoryCorner_eq_convexHull_mixed_integer_points
    [Fintype I]
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    tableauToMixedPointEquiv '' gomory_corner_polyhedron abar bbar =
      convexHull ℝ
        (mixed_integer_points
          (tableauToMixedPointEquiv '' rationalTableauCornerRelaxation abar bbar)) := by
  rw [gomory_corner_polyhedron_eq_convexHull]
  calc
    tableauToMixedPointEquiv ''
        convexHull ℝ (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice)
        =
          convexHull ℝ
            (tableauToMixedPointEquiv ''
              (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice)) := by
            simpa using
              (tableauToMixedPointEquiv (I := I) (N := N)).toLinearMap.image_convexHull
                (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice)
    _ = convexHull ℝ
          ((tableauToMixedPointEquiv '' rationalTableauCornerRelaxation abar bbar) ∩
            mixed_integer_lattice (Fintype.card I) (Fintype.card N)) := by
          congr 1
          ext xy
          constructor
          · rintro ⟨x, ⟨hxP, hxL⟩, rfl⟩
            constructor
            · exact ⟨x, hxP, rfl⟩
            · have hxy :
                tableauToMixedPointEquiv x ∈
                  tableauToMixedPointEquiv '' tableau_mixed_integer_lattice :=
                  ⟨x, hxL, rfl⟩
              simpa [tableauToMixedPoint_image_tableauMixedIntegerLattice_eq_mixed_integer_lattice
                (I := I) (N := N)] using hxy
          · rintro ⟨hxyP, hxyL⟩
            rcases hxyP with ⟨x, hxP, rfl⟩
            have himage :
                tableauToMixedPointEquiv x ∈
                  tableauToMixedPointEquiv '' tableau_mixed_integer_lattice := by
              simpa [tableauToMixedPoint_image_tableauMixedIntegerLattice_eq_mixed_integer_lattice
                (I := I) (N := N)] using hxyL
            rcases himage with ⟨x', hxL, hx'eq⟩
            have hxx' : x' = x := (tableauToMixedPointEquiv (I := I) (N := N)).injective <| by
              simpa using hx'eq
            subst hxx'
            exact ⟨x', ⟨hxP, hxL⟩, rfl⟩
    _ = convexHull ℝ
          (mixed_integer_points
            (tableauToMixedPointEquiv '' rationalTableauCornerRelaxation abar bbar)) := by
          rfl

section PolyhedralResult

variable [Fintype I]

/-- Lemma 6.2 (1). If the affine hull of `P(B)` contains a point of the tableau-coordinate
mixed-integer lattice `ℤ^p × ℝ^(n - p)`, then the canonical `Fin`-coordinate view of `corner(B)`
is a polyhedron. -/
theorem gomory_corner_polyhedron_is_polyhedron_of_affineSpan_has_mixed_integer_point
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (h_affine : tableauAffineSpanHasMixedIntegerPoint abar bbar) :
    is_polyhedron (finCoordinateSet (gomory_corner_polyhedron abar bbar)) := by
  have _ := h_affine
  let e :
      Fin (Fintype.card (Sum I N)) ≃ Fin (Fintype.card I + Fintype.card N) :=
    (Fintype.equivFin (Sum I N)).symm.trans
      (tableauCoordinateEquiv (I := I) (N := N)).symm
  let Ptab : Set (MixedRealPoint (Fintype.card I) (Fintype.card N)) :=
    tableauToMixedPointEquiv '' rationalTableauCornerRelaxation abar bbar
  have hPtab : is_rational_mixed_polyhedron Ptab := by
    rcases tableauToMixedPoint_image_rationalTableauCornerRelaxation_eq_rationalMixedPolyhedron
        (I := I) (N := N) abar bbar with ⟨m, A, G, b, hPtabEq⟩
    -- The transported relaxation already has an explicit rational mixed-system presentation.
    simpa [Ptab, hPtabEq] using
      (is_rational_mixed_polyhedron_iff).2 ⟨m, A, G, b, rfl⟩
  have hHullMixed :
      is_rational_mixed_polyhedron
        (tableauToMixedPointEquiv '' gomory_corner_polyhedron abar bbar) := by
    -- Route correction: use the earlier local mixed-hull theorem directly on the transported
    -- corner hull, instead of importing the later Chapter 4 wrapper that currently drags in a
    -- broken downstream dependency chain.
    rw [image_gomoryCorner_eq_convexHull_mixed_integer_points (I := I) (N := N) abar bbar]
    exact Theorem15Support.mixed_integer_hull_is_rational_mixed_polyhedron_local
      (P := Ptab) hPtab
  have hFlatPoly :
      is_polyhedron
        ((Fin.appendEquiv (Fintype.card I) (Fintype.card N)) ''
          (tableauToMixedPointEquiv '' gomory_corner_polyhedron abar bbar)) := by
    have hFlatRat :
        is_rational_polyhedron
          ((Fin.appendEquiv (Fintype.card I) (Fintype.card N)) ''
            (tableauToMixedPointEquiv '' gomory_corner_polyhedron abar bbar)) := by
      simpa [is_rational_mixed_polyhedron] using hHullMixed
    rcases hFlatRat with ⟨m, A, b, hFlatEq⟩
    exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), hFlatEq⟩
  have hReindexed :
      is_polyhedron
        ((LinearEquiv.funCongrLeft ℝ ℝ e) ''
          ((Fin.appendEquiv (Fintype.card I) (Fintype.card N)) ''
            (tableauToMixedPointEquiv '' gomory_corner_polyhedron abar bbar))) := by
    -- Reindex the split flattening back to the local `finCoordinateSet` owner.
    exact is_polyhedron_image_funCongrLeft e hFlatPoly
  -- The composed reindexing is exactly the canonical `finCoordinateSet` view.
  have hCompose :
      (fun x : Sum I N → ℝ ↦
        (LinearMap.funLeft ℝ ℝ ⇑e)
          (Fin.appendEquiv (Fintype.card I) (Fintype.card N) (tableauToMixedPointEquiv x))) =
      (fun x : Sum I N → ℝ ↦
        (LinearMap.funLeft ℝ ℝ ⇑(Fintype.equivFin (I ⊕ N)).symm) x) := by
    funext x
    ext t
    rw [appendEquiv_tableauToMixedPointEquiv_eq_tableauFlatEquiv (I := I) (N := N) x]
    simp [e, tableauCoordinateEquiv, LinearEquiv.funCongrLeft, LinearMap.funLeft]
  simpa [finCoordinateSet, Set.image_image, hCompose] using hReindexed

end PolyhedralResult

/-- Lemma 6.2 (2). If the affine hull of `P(B)` contains a point of the tableau-coordinate
mixed-integer lattice `ℤ^p × ℝ^(n - p)`, then `corner(B)` has affine dimension `|N|`. -/
theorem affine_dim_gomory_corner_polyhedron_eq_card_of_affineSpan_has_mixed_integer_point
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    [Finite I]
    (h_affine : tableauAffineSpanHasMixedIntegerPoint abar bbar) :
    Module.finrank ℝ (affineSpan ℝ (gomory_corner_polyhedron abar bbar)).direction =
      Fintype.card N := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  rcases
      exists_mixedIntegerPoint_mem_rationalTableauCornerRelaxation_of_affineSpanHasMixedIntegerPoint
        (I := I) (N := N) abar bbar h_affine with
    ⟨x0, hx0_relax, hx0_lattice⟩
  let Hcorner : AffineSubspace ℝ (Sum I N → ℝ) :=
    affineSpan ℝ (gomory_corner_polyhedron abar bbar)
  have hray :
      ∀ j : N, tableauCornerRay abar j ∈ Hcorner.direction := by
    intro j
    simpa [Hcorner] using
      tableauCornerRay_mem_direction_affineSpan_gomory_corner_polyhedron
        (I := I) (N := N) abar bbar hx0_relax hx0_lattice j
  have hspan_le :
      Submodule.span ℝ (Set.range (tableauCornerRay abar)) ≤ Hcorner.direction := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact hray j
  have hlower :
      Fintype.card N ≤ Module.finrank ℝ Hcorner.direction := by
    calc
      Fintype.card N
          = Module.finrank ℝ (Submodule.span ℝ (Set.range (tableauCornerRay abar))) := by
              symm
              simpa using finrank_span_eq_card (tableauCornerRay_linearIndependent abar)
      _ ≤ Module.finrank ℝ Hcorner.direction := by
            exact Submodule.finrank_mono hspan_le
  have hcorner_subset_tableau :
      gomory_corner_polyhedron abar bbar ⊆ tableauAffineHull abar bbar := by
    rw [gomory_corner_polyhedron_eq_convexHull]
    refine convexHull_min ?_ (tableauAffineHull abar bbar).convex
    intro x hx
    exact rationalTableauCornerRelaxation_subset_tableauAffineHull abar bbar hx.1
  have hcorner_le :
      Hcorner ≤ tableauAffineHull abar bbar := by
    exact affineSpan_le.2 hcorner_subset_tableau
  have hupper :
      Module.finrank ℝ Hcorner.direction ≤ Fintype.card N := by
    calc
      Module.finrank ℝ Hcorner.direction
          ≤ Module.finrank ℝ (tableauAffineHull abar bbar).direction := by
              exact Submodule.finrank_mono (AffineSubspace.direction_le hcorner_le)
      _ = Module.finrank ℝ
            (affineSpan ℝ (rationalTableauCornerRelaxation abar bbar)).direction := by
              rw [affineSpan_rationalTableauCornerRelaxation_eq_tableauAffineHull]
      _ = Fintype.card N := by
            exact finrank_direction_affineSpan_rationalTableauCornerRelaxation_eq_card abar bbar
  exact le_antisymm hupper hlower

/-- Lemma 6.2 (3). If the affine hull of `P(B)` contains no point of the tableau-coordinate
mixed-integer lattice `ℤ^p × ℝ^(n - p)`, then `corner(B)` is empty. -/
theorem gomory_corner_polyhedron_eq_empty_of_no_mixed_integer_point_in_affineSpan
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (h_affine : ¬ tableauAffineSpanHasMixedIntegerPoint abar bbar) :
    gomory_corner_polyhedron abar bbar = ∅ := by
  -- Any mixed-integer tableau-feasible point already lies in the affine hull of the tableau
  -- relaxation, so the assumption rules out every generator of the hull.
  rw [gomory_corner_polyhedron_eq_convexHull]
  have hGeneratorsEmpty :
      rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice = ∅ := by
    ext x
    constructor
    · intro hx
      have hx_aff :
          x ∈ affineSpan ℝ (rationalTableauCornerRelaxation abar bbar) :=
        subset_affineSpan ℝ _ hx.1
      exact False.elim <| h_affine ⟨x, hx_aff, hx.2⟩
    · intro hx
      simp at hx
  rw [hGeneratorsEmpty]
  exact convexHull_empty

end Tableau

end Lemma62
