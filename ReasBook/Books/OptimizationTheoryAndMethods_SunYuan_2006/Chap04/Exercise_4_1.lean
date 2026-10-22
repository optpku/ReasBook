/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Definition_4_1_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators

section

variable {n : ℕ}

local notation "Vector" => Fin n → ℝ

private noncomputable def chapter04Exercise41DirectionsAux
    (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Vector) : ℕ → Vector
  | 0 => if h0 : 0 < n then p ⟨0, h0⟩ else 0
  | k + 1 =>
      if hk : k + 1 < n then
        let B := G.toBilin'
        let pk : Vector := p ⟨k + 1, hk⟩
        pk -
          ∑ i : Fin (k + 1),
            ((B pk (chapter04Exercise41DirectionsAux G p i)) /
                (B (chapter04Exercise41DirectionsAux G p i)
                  (chapter04Exercise41DirectionsAux G p i))) •
              chapter04Exercise41DirectionsAux G p i
      else 0
termination_by k => k
decreasing_by
  simpa using i.2

/-- The explicit `G`-weighted Gram-Schmidt recurrence from Exercise 4.1, indexed by the source
family `p : Fin n → Vector`. -/
noncomputable def chapter04Exercise41Directions
    (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Vector) : Fin n → Vector :=
  fun i ↦ chapter04Exercise41DirectionsAux G p i

/-- The recurrence starts from `d₁ = p₁`. -/
theorem chapter04Exercise41Directions_zero
    (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Vector) (hn : 0 < n) :
    chapter04Exercise41Directions G p ⟨0, hn⟩ = p ⟨0, hn⟩ := by
  -- Unfold the auxiliary recursion at the initial index and take the active branch.
  simp [chapter04Exercise41Directions, chapter04Exercise41DirectionsAux, hn]

/-- The successor step matches the textbook `G`-weighted projection formula. -/
theorem chapter04Exercise41Directions_succ
    (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Vector) {k : ℕ} (hk : k + 1 < n) :
    chapter04Exercise41Directions G p ⟨k + 1, hk⟩ =
      let d := chapter04Exercise41Directions G p
      let dPrev : Fin (k + 1) → Vector := fun i ↦ d ⟨i, Nat.lt_trans i.2 hk⟩
      let B := G.toBilin'
      let pk : Vector := p ⟨k + 1, hk⟩
      pk -
        ∑ i : Fin (k + 1),
          ((B pk (dPrev i)) / (B (dPrev i) (dPrev i))) • dPrev i := by
  -- Unfold the successor branch and rewrite recursive calls through the exported family.
  simp [chapter04Exercise41Directions, chapter04Exercise41DirectionsAux, hk]

/-- Helper for Chapter04 Exercise 4.1: the bilinear pairing `xᵀ G y` is symmetric when `G` is
positive definite. -/
private theorem chapter04Exercise41_dotProduct_mulVec_comm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (u v : Vector) :
    dotProduct u (G.mulVec v) = dotProduct v (G.mulVec u) := by
  -- Positive definiteness gives symmetry, so the transpose-switching identity closes the goal.
  have hsymm : G.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using (show G.IsHermitian from hG.1)
  simpa [hsymm.eq] using Matrix.dotProduct_transpose_mulVec G u v

/-- Helper for Chapter04 Exercise 4.1: each nonempty prefix of the weighted Gram-Schmidt family
spans the same subspace as the corresponding prefix of the source family. -/
private theorem chapter04Exercise41_prefix_span_eq
    (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Vector) :
    ∀ {k : ℕ} (hk : k < n),
      let dPrefix : Fin (k + 1) → Vector :=
        fun i ↦ chapter04Exercise41Directions G p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩
      let pPrefix : Fin (k + 1) → Vector :=
        fun i ↦ p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩
      Submodule.span ℝ (Set.range dPrefix) = Submodule.span ℝ (Set.range pPrefix)
  | k, hk => by
      induction k with
      | zero =>
          -- The first direction is exactly the first source vector, so the singleton spans agree.
          have hsingleton :
              (fun i : Fin 1 ↦ chapter04Exercise41Directions G p ⟨i, Nat.lt_of_lt_of_le i.2
                  (Nat.succ_le_of_lt hk)⟩) =
                fun i : Fin 1 ↦ p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩ := by
            funext i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            simp [chapter04Exercise41Directions_zero]
          exact congrArg (fun f ↦ Submodule.span ℝ (Set.range f)) hsingleton
      | succ k ih =>
          let d := chapter04Exercise41Directions G p
          let dOld : Fin (k + 1) → Vector := fun i ↦ d ⟨i,
            Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_of_succ_lt hk))⟩
          let pOld : Fin (k + 1) → Vector := fun i ↦ p ⟨i,
            Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_of_succ_lt hk))⟩
          let dLast : Vector := d ⟨k + 1, hk⟩
          let pLast : Vector := p ⟨k + 1, hk⟩
          let B := G.toBilin'
          let correction : Vector :=
            ∑ i : Fin (k + 1), ((B pLast (dOld i)) / (B (dOld i) (dOld i))) • dOld i
          let dNew : Fin (k + 2) → Vector := Fin.snoc dOld dLast
          let pNew : Fin (k + 2) → Vector := Fin.snoc pOld pLast
          have hOld :
              Submodule.span ℝ (Set.range dOld) = Submodule.span ℝ (Set.range pOld) := by
            simpa [d, dOld, pOld] using ih (Nat.lt_of_succ_lt hk)
          have hdNew :
              (fun i : Fin (k + 2) ↦ d ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩) =
                dNew := by
            funext i
            obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · simp [dNew, dOld]
            · simp [dNew, dLast]
          have hpNew :
              (fun i : Fin (k + 2) ↦ p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩) =
                pNew := by
            funext i
            obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · simp [pNew, pOld]
            · simp [pNew, pLast]
          have hOldIntoNew : Set.range pOld ⊆ Set.range pNew := by
            rintro x ⟨i, rfl⟩
            exact ⟨i.castSucc, by simp [pNew]⟩
          have hOldIntoNew' : Set.range dOld ⊆ Set.range dNew := by
            rintro x ⟨i, rfl⟩
            exact ⟨i.castSucc, by simp [dNew]⟩
          have hdLast_formula : dLast = pLast - correction := by
            simpa [d, dOld, dLast, pLast, B, correction] using
              chapter04Exercise41Directions_succ G p hk
          rw [hdNew, hpNew]
          apply le_antisymm
          · -- Every new direction lies in the span of the enlarged source prefix.
            refine Submodule.span_le.2 ?_
            rintro x ⟨i, rfl⟩
            obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · have hmemOld : dOld j ∈ Submodule.span ℝ (Set.range pOld) := by
                rw [← hOld]
                exact Submodule.subset_span ⟨j, rfl⟩
              simpa [dNew] using (Submodule.span_mono hOldIntoNew) hmemOld
            · have hpLastMem : pLast ∈ Submodule.span ℝ (Set.range pNew) :=
                Submodule.subset_span ⟨Fin.last (k + 1), by simp [pNew]⟩
              have hCorrectionMem : correction ∈ Submodule.span ℝ (Set.range pNew) := by
                refine Submodule.sum_mem _ ?_
                intro j _
                have hmemOld : dOld j ∈ Submodule.span ℝ (Set.range pOld) := by
                  rw [← hOld]
                  exact Submodule.subset_span ⟨j, rfl⟩
                exact Submodule.smul_mem _ _ ((Submodule.span_mono hOldIntoNew) hmemOld)
              simpa [dNew] using
                (show dLast ∈ Submodule.span ℝ (Set.range pNew) by
                  rw [hdLast_formula]
                  exact Submodule.sub_mem _ hpLastMem hCorrectionMem)
          · -- Conversely, the new source vector is recovered from the recurrence relation.
            refine Submodule.span_le.2 ?_
            rintro x ⟨i, rfl⟩
            obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · have hmemOld : pOld j ∈ Submodule.span ℝ (Set.range dOld) := by
                rw [hOld]
                exact Submodule.subset_span ⟨j, rfl⟩
              simpa [pNew] using (Submodule.span_mono hOldIntoNew') hmemOld
            · have hdLastMem : dLast ∈ Submodule.span ℝ (Set.range dNew) :=
                Submodule.subset_span ⟨Fin.last (k + 1), by simp [dNew]⟩
              have hCorrectionMem : correction ∈ Submodule.span ℝ (Set.range dNew) := by
                refine Submodule.sum_mem _ ?_
                intro j _
                exact Submodule.smul_mem _ _
                  (Submodule.subset_span ⟨j.castSucc, by simp [dNew]⟩)
              have hpLast_formula : pLast = dLast + correction := by
                exact sub_eq_iff_eq_add.mp hdLast_formula.symm
              simpa [pNew] using
                (show pLast ∈ Submodule.span ℝ (Set.range dNew) by
                  rw [hpLast_formula]
                  exact Submodule.add_mem _ hdLastMem hCorrectionMem)

/-- Helper for Chapter04 Exercise 4.1: after orthogonalizing against a conjugate prefix, the new
direction is `G`-orthogonal to every vector in that prefix. -/
private theorem chapter04Exercise41_direction_orthogonal_prefix
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (p : Fin n → Vector)
    {k : ℕ} (hk : k + 1 < n)
    (hPrefix :
      let dPrefix : Fin (k + 1) → Vector :=
        fun i ↦ chapter04Exercise41Directions G p ⟨i,
          Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self k) hk))⟩
      G.IsConjugateFamily dPrefix) :
    let d := chapter04Exercise41Directions G p
    let dPrefix : Fin (k + 1) → Vector := fun i ↦ d ⟨i,
      Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self k) hk))⟩
    ∀ i : Fin (k + 1), dotProduct (dPrefix i) (G.mulVec (d ⟨k + 1, hk⟩)) = 0 := by
  let d := chapter04Exercise41Directions G p
  let dPrefix : Fin (k + 1) → Vector := fun i ↦ d ⟨i,
    Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self k) hk))⟩
  let B := G.toBilin'
  let pLast : Vector := p ⟨k + 1, hk⟩
  let coeff : Fin (k + 1) → ℝ := fun i ↦ (B pLast (dPrefix i)) / (B (dPrefix i) (dPrefix i))
  change ∀ i : Fin (k + 1), dotProduct (dPrefix i) (G.mulVec (d ⟨k + 1, hk⟩)) = 0
  have hPrefix' : G.IsConjugateFamily dPrefix := by
    simpa [d, dPrefix] using hPrefix
  have hPair := (Matrix.isConjugateFamily_iff.mp hPrefix').2
  have hdLast_formula :
      d ⟨k + 1, hk⟩ = pLast - ∑ j : Fin (k + 1), coeff j • dPrefix j := by
    simpa [d, dPrefix, B, pLast, coeff] using chapter04Exercise41Directions_succ G p hk
  intro i
  -- Positive definiteness guarantees the diagonal term used in the projection is nonzero.
  have hdiag_ne : B (dPrefix i) (dPrefix i) ≠ 0 := by
    have hpos : 0 < dotProduct (dPrefix i) (G.mulVec (dPrefix i)) := by
      simpa [d, dPrefix] using hG.dotProduct_mulVec_pos (hPrefix'.nonzero i)
    simpa [B, Matrix.toBilin'_apply'] using ne_of_gt hpos
  -- Collapse the correction sum to its diagonal contribution using prefix conjugacy.
  have hsum :
      B (dPrefix i) (∑ j : Fin (k + 1), coeff j • dPrefix j) =
        coeff i * B (dPrefix i) (dPrefix i) := by
    rw [LinearMap.BilinForm.sum_right]
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.BilinForm.smul_right]
    · intro j _ hij
      rw [LinearMap.BilinForm.smul_right]
      have hzero : B (dPrefix i) (dPrefix j) = 0 := by
        simpa [B, Matrix.toBilin'_apply'] using hPair i j (by simpa [eq_comm] using hij)
      simp [hzero]
    · intro hi
      simp at hi
  -- Symmetry converts the left factor against `pLast` into the coefficient numerator.
  have hsym : B (dPrefix i) pLast = B pLast (dPrefix i) := by
    simpa [B, Matrix.toBilin'_apply'] using
      chapter04Exercise41_dotProduct_mulVec_comm G hG (dPrefix i) pLast
  -- After expanding once, the diagonal correction cancels exactly with the numerator term.
  calc
    dotProduct (dPrefix i) (G.mulVec (d ⟨k + 1, hk⟩))
        = B (dPrefix i) (d ⟨k + 1, hk⟩) := by
            simp [B, Matrix.toBilin'_apply']
    _ = B (dPrefix i) (pLast - ∑ j : Fin (k + 1), coeff j • dPrefix j) := by
          rw [hdLast_formula]
    _ = B (dPrefix i) pLast - B (dPrefix i) (∑ j : Fin (k + 1), coeff j • dPrefix j) := by
          rw [LinearMap.BilinForm.sub_right]
    _ = B pLast (dPrefix i) - coeff i * B (dPrefix i) (dPrefix i) := by
          rw [hsum, hsym]
    _ = 0 := by
          dsimp [coeff]
          field_simp [hdiag_ne]
          ring

/-- Helper for Chapter04 Exercise 4.1: every successor direction in the weighted Gram-Schmidt
construction is nonzero. -/
private theorem chapter04Exercise41_direction_succ_ne
    (G : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → Vector) (hp : LinearIndependent ℝ p)
    {k : ℕ} (hk : k + 1 < n) :
    chapter04Exercise41Directions G p ⟨k + 1, hk⟩ ≠ 0 := by
  let d := chapter04Exercise41Directions G p
  let dOld : Fin (k + 1) → Vector := fun i ↦ d ⟨i,
    Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self k) hk))⟩
  let pOld : Fin (k + 1) → Vector := fun i ↦ p ⟨i,
    Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_trans (Nat.lt_succ_self k) hk))⟩
  let dLast : Vector := d ⟨k + 1, hk⟩
  let pLast : Vector := p ⟨k + 1, hk⟩
  let B := G.toBilin'
  let correction : Vector :=
    ∑ i : Fin (k + 1), ((B pLast (dOld i)) / (B (dOld i) (dOld i))) • dOld i
  intro hzero
  have hdLast_formula : dLast = pLast - correction := by
    simpa [d, dOld, dLast, pLast, B, correction] using
      chapter04Exercise41Directions_succ G p hk
  -- If the new direction vanished, the new source vector would lie in the old direction span.
  have hdLast_zero : dLast = 0 := by
    simpa [d, dLast] using hzero
  have hpLast_eq_correction : pLast = correction := by
    have hsub : pLast - correction = 0 := by
      rw [← hdLast_formula, hdLast_zero]
    exact sub_eq_zero.mp hsub
  have hCorrectionMem : correction ∈ Submodule.span ℝ (Set.range dOld) := by
    refine Submodule.sum_mem _ ?_
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hpLastMemOld : pLast ∈ Submodule.span ℝ (Set.range dOld) := by
    rw [hpLast_eq_correction]
    exact hCorrectionMem
  -- Transport that span membership back to the old source prefix.
  have hOldSpan : Submodule.span ℝ (Set.range dOld) = Submodule.span ℝ (Set.range pOld) := by
    simpa [d, dOld, pOld] using
      chapter04Exercise41_prefix_span_eq G p (k := k) (Nat.lt_trans (Nat.lt_succ_self k) hk)
  have hpLastMemPOld : pLast ∈ Submodule.span ℝ (Set.range pOld) := by
    rw [hOldSpan] at hpLastMemOld
    exact hpLastMemOld
  let oldIndices : Set (Fin n) :=
    Set.range fun i : Fin (k + 1) ↦ (⟨i, Nat.lt_trans i.2 hk⟩ : Fin n)
  have hOldImage : Set.range pOld ⊆ p '' oldIndices := by
    rintro x ⟨i, rfl⟩
    exact ⟨⟨i, Nat.lt_trans i.2 hk⟩, ⟨i, rfl⟩, rfl⟩
  have hpLastMemImage : pLast ∈ Submodule.span ℝ (p '' oldIndices) := by
    exact (Submodule.span_mono hOldImage) hpLastMemPOld
  have hlast_not_mem : (⟨k + 1, hk⟩ : Fin n) ∉ oldIndices := by
    rintro ⟨i, hi⟩
    have hval : i.1 = k + 1 := by
      simpa using congrArg Fin.val hi
    exact (Nat.ne_of_lt i.2 hval).elim
  -- Linear independence forbids the new source vector from lying in the span of the old ones.
  exact
    (show pLast ∉ Submodule.span ℝ (p '' oldIndices) by
      simpa [pLast] using
        (hp.notMem_span_image (s := oldIndices) (x := (⟨k + 1, hk⟩ : Fin n)) hlast_not_mem))
      hpLastMemImage

/-- Helper for Chapter04 Exercise 4.1: every nonempty prefix of the weighted Gram-Schmidt family
is already `G`-conjugate. -/
private theorem chapter04Exercise41_prefix_isConjugate
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (p : Fin n → Vector)
    (hp : LinearIndependent ℝ p) :
    ∀ {k : ℕ} (hk : k < n),
      let dPrefix : Fin (k + 1) → Vector :=
        fun i ↦ chapter04Exercise41Directions G p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩
      G.IsConjugateFamily dPrefix
  | k, hk => by
      induction k with
      | zero =>
          -- The singleton prefix is conjugate because its sole vector is nonzero.
          rw [Matrix.isConjugateFamily_iff]
          constructor
          · intro i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            simpa [chapter04Exercise41Directions_zero, hk] using hp.ne_zero ⟨0, hk⟩
          · intro i j hij
            have hi : i = 0 := Fin.eq_zero i
            have hj : j = 0 := Fin.eq_zero j
            subst i
            subst j
            exact (hij rfl).elim
      | succ k ih =>
          let d := chapter04Exercise41Directions G p
          let dOld : Fin (k + 1) → Vector := fun i ↦ d ⟨i,
            Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt (Nat.lt_of_succ_lt hk))⟩
          let dLast : Vector := d ⟨k + 1, hk⟩
          let dNew : Fin (k + 2) → Vector := Fin.snoc dOld dLast
          have hdNew :
              (fun i : Fin (k + 2) ↦ d ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩) =
                dNew := by
            funext i
            obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · simp [dNew, dOld]
            · simp [dNew, dLast]
          have hPrev : G.IsConjugateFamily dOld := by
            simpa [d, dOld] using ih (Nat.lt_of_succ_lt hk)
          rw [hdNew, Matrix.isConjugateFamily_iff]
          constructor
          · -- Old vectors stay nonzero, and the new vector is handled by the span contradiction.
            intro i
            obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · simpa [dNew] using hPrev.nonzero j
            · simpa [dNew, dLast, d] using chapter04Exercise41_direction_succ_ne G p hp hk
          · -- Orthogonality splits into old-old, old-new, and new-old cases.
            intro i j hij
            obtain ⟨i', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
            · obtain ⟨j', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
              · simpa [dNew] using
                  (Matrix.isConjugateFamily_iff.mp hPrev).2 i' j' fun hEq ↦
                    by
                      cases hEq
                      exact hij rfl
              · simpa [dNew, dOld, dLast, d] using
                  chapter04Exercise41_direction_orthogonal_prefix G hG p hk hPrev i'
            · obtain ⟨j', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
              · have hOldNew :
                    dotProduct (dOld j') (G.mulVec dLast) = 0 := by
                  simpa [dOld, dLast, d] using
                    chapter04Exercise41_direction_orthogonal_prefix G hG p hk hPrev j'
                simpa [dNew] using
                  (calc
                    dotProduct dLast (G.mulVec (dOld j'))
                        = dotProduct (dOld j') (G.mulVec dLast) := by
                            exact chapter04Exercise41_dotProduct_mulVec_comm G hG dLast (dOld j')
                    _ = 0 := hOldNew)
              · exact (hij rfl).elim

/-- Helper for Chapter04 Exercise 4.1: every nonempty prefix of the weighted Gram-Schmidt
directions is already `G`-conjugate and spans the same subspace as the corresponding prefix of the
source family. -/
private theorem chapter04Exercise41_prefix_properties
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (p : Fin n → Vector)
    (hp : LinearIndependent ℝ p) :
    ∀ {k : ℕ} (hk : k < n),
      let dPrefix : Fin (k + 1) → Vector :=
        fun i ↦ chapter04Exercise41Directions G p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩
      let pPrefix : Fin (k + 1) → Vector :=
        fun i ↦ p ⟨i, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk)⟩
      G.IsConjugateFamily dPrefix ∧
        Submodule.span ℝ (Set.range dPrefix) = Submodule.span ℝ (Set.range pPrefix)
  | k, hk => by
      -- The textbook proof splits cleanly into prefix conjugacy and prefix span preservation.
      exact ⟨chapter04Exercise41_prefix_isConjugate G hG p hp hk,
        chapter04Exercise41_prefix_span_eq G p hk⟩

/-- Chapter04 Exercise 4.1: if `G` is a symmetric positive definite real matrix and
`p : Fin n → Fin n → ℝ` is linearly independent, then the family obtained from the textbook
recurrence `d₁ = p₁` and
`d_{k+1} = p_{k+1} - ∑_{i=1}^k ((p_{k+1}ᵀ G d_i) / (d_iᵀ G d_i)) • d_i`
is `G`-conjugate. -/
theorem chapter04Exercise41_isConjugateFamily
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (p : Fin n → Vector)
    (hp : LinearIndependent ℝ p) :
    G.IsConjugateFamily (chapter04Exercise41Directions G p) := by
  cases n with
  | zero =>
      -- The empty family is conjugate vacuously.
      rw [Matrix.isConjugateFamily_iff]
      simp [chapter04Exercise41Directions]
  | succ k =>
      -- The prefix theorem at the final index gives the full family immediately.
      simpa using
        (chapter04Exercise41_prefix_properties (n := k + 1) G hG p hp
          (k := k) (Nat.lt_succ_self k)).1

end
