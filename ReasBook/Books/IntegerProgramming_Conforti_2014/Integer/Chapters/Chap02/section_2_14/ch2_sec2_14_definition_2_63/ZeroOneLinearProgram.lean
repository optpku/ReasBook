/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_3

open scoped Matrix MixedIntegerNotation

namespace ZeroOneLinearProgram

variable {m n : ℕ}

/-- The canonical Chapter 1 mixed integer linear program encoding the `0`--`1` linear program
with objective coefficients `c`, constraint matrix `A`, right-hand side `b`, no continuous
variables, and an added upper-bound block enforcing `x ≤ 1`. -/
def toMixedIntegerLinearProgram
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    MixedIntegerLinearProgram (m + n) n 0 :=
  MixedIntegerLinearProgram.ofCoefficients
    (fun r j ↦
      Fin.addCases
        (fun i : Fin m ↦ ((A.map (Int.castRingHom ℝ)) i j))
        (fun i : Fin n ↦ if i = j then 1 else 0)
        r)
    0
    (Fin.addCases (fun i : Fin m ↦ (b i : ℝ)) (fun _ : Fin n ↦ 1))
    (fun j ↦ (c j : ℝ))
    0

/-- The feasible set of the `0`--`1` linear program with data `(c, A, b)` consists of the real
vectors satisfying `A x ≤ b` whose coordinates are all `0` or `1`. -/
def feasibleSet
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    Set (Fin n → ℝ) :=
  {x | (x, fun i ↦ Fin.elim0 i) ∈ (toMixedIntegerLinearProgram c A b).mixedZeroOneFeasibleSet}

/-- Membership in `feasibleSet c A b` is exactly the conjunction of the linear system
`A x ≤ b` and the binary coordinate conditions `x j = 0 ∨ x j = 1`. -/
theorem mem_feasibleSet_iff
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {x : Fin n → ℝ} :
    x ∈ feasibleSet c A b ↔
      ((A.map (Int.castRingHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ)) ∧
        ∀ j : Fin n, x j = 0 ∨ x j = 1 := by
  -- Read the stacked mixed-`0,1` constraints rowwise and discard the redundant upper-bound
  -- block when passing back to the source-facing formulation.
  rw [feasibleSet, Set.mem_setOf_eq]
  rw [(toMixedIntegerLinearProgram c A b).mem_mixedZeroOneFeasibleSet_iff (x, fun i ↦ Fin.elim0 i)]
  constructor
  · rintro ⟨hineq, hx_binary, _⟩
    refine ⟨?_, hx_binary⟩
    intro i
    simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
      Matrix.mulVec, dotProduct] using hineq (Fin.castAdd n i)
  · rintro ⟨hineq, hx_binary⟩
    refine ⟨?_, hx_binary, ?_⟩
    · intro r
      refine Fin.addCases ?_ ?_ r
      · intro i
        simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
          Matrix.mulVec, dotProduct] using hineq i
      · intro j
        rcases hx_binary j with hj | hj
        · simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
            Matrix.mulVec, dotProduct, hj]
        · simp [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
            Matrix.mulVec, dotProduct, hj]
    · intro i
      exact Fin.elim0 i

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_63/ZeroOneLinearProgram.lean:
an integer whose real cast lies in `[0, 1]` is `0` or `1`. -/
lemma intCast_eq_zero_or_one_of_nonneg_le_one
    {z : ℤ}
    (hz_nonneg : 0 ≤ (z : ℝ))
    (hz_le_one : (z : ℝ) ≤ 1) :
    z = 0 ∨ z = 1 := by
  -- Pull the real bounds back to `ℤ` and close the remaining arithmetic there.
  have hz_nonneg' : 0 ≤ z := by
    exact_mod_cast hz_nonneg
  have hz_le_one' : z ≤ 1 := by
    exact_mod_cast hz_le_one
  omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_63/ZeroOneLinearProgram.lean:
every function on `Fin 0` is the canonical empty function. -/
lemma finZeroFunction_eq_elim0
    {α : Sort*}
    (f : Fin 0 → α) :
    f = fun i ↦ Fin.elim0 i := by
  -- Function extensionality leaves an impossible `Fin 0` input.
  funext i
  exact Fin.elim0 i

/-- The source-facing feasible vectors are exactly the feasible points of the canonical Chapter 1
MILP bridge with empty continuous block. -/
theorem mem_toMixedIntegerLinearProgram_feasibleSet_iff
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {x : Fin n → ℝ} :
    (x, fun i ↦ Fin.elim0 i) ∈ (toMixedIntegerLinearProgram c A b).feasibleSet ↔
      x ∈ feasibleSet c A b := by
  constructor
  · intro hx
    -- Extract the Chapter 1 MILP inequalities and integrality witnesses, then compress them to
    -- the source-facing binary description.
    rw [(toMixedIntegerLinearProgram c A b).mem_feasibleSet_iff (x, fun i ↦ Fin.elim0 i)] at hx
    rcases hx with ⟨hineq, hx_nonneg, _, hint⟩
    refine mem_feasibleSet_iff.mpr ⟨?_, ?_⟩
    · intro i
      simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
        Matrix.mulVec, dotProduct] using hineq (Fin.castAdd n i)
    · intro j
      have hj_nonneg : 0 ≤ x j := hx_nonneg j
      have hj_le_one : x j ≤ 1 := by
        simpa [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
          Matrix.mulVec, dotProduct] using hineq (Fin.natAdd m j)
      rcases hint j with ⟨z, hz⟩
      have hz_cast : x j = (z : ℝ) := hz
      have hz_nonneg : 0 ≤ (z : ℝ) := by
        rw [← hz_cast]
        exact hj_nonneg
      have hz_le_one : (z : ℝ) ≤ 1 := by
        rw [← hz_cast]
        exact hj_le_one
      rcases intCast_eq_zero_or_one_of_nonneg_le_one hz_nonneg hz_le_one with hz_zero | hz_one
      · left
        simpa [hz_zero] using hz_cast
      · right
        simpa [hz_one] using hz_cast
  · intro hx
    -- Any source-feasible point is already mixed-`0,1` feasible, hence feasible for the MILP.
    have hmixed : (x, fun i ↦ Fin.elim0 i) ∈
        (toMixedIntegerLinearProgram c A b).mixedZeroOneFeasibleSet := by
      simpa [feasibleSet] using hx
    exact
      (toMixedIntegerLinearProgram c A b).mixedZeroOneFeasibleSet_subset_feasibleSet hmixed

/-- The objective value of the `0`--`1` linear program with objective coefficients `c` at a
vector `x` is the dot product `c ⬝ᵥ x` after coercing `c` to `ℝ`. -/
def objectiveValue
    (c : Fin n → ℤ)
    (x : Fin n → ℝ) : ℝ :=
  (fun j ↦ (c j : ℝ)) ⬝ᵥ x

/-- Unfolding equation for `objectiveValue c x`. -/
theorem objectiveValue_def
    {c : Fin n → ℤ}
    {x : Fin n → ℝ} :
    objectiveValue c x = (fun j ↦ (c j : ℝ)) ⬝ᵥ x := by
  -- This is the defining equation of the source objective wrapper.
  rfl

/-- The source-facing objective agrees with the Chapter 1 MILP objective on the empty continuous
block. -/
theorem objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {x : Fin n → ℝ} :
    objectiveValue c x =
      (toMixedIntegerLinearProgram c A b).objectiveValue (x, fun i ↦ Fin.elim0 i) := by
  -- Expand the Chapter 1 objective and collapse the empty continuous block.
  rw [objectiveValue_def, (toMixedIntegerLinearProgram c A b).objectiveValue_def]
  simp only [toMixedIntegerLinearProgram, MixedIntegerLinearProgram.ofCoefficients,
    Int.coe_castRingHom, Matrix.map_apply, Matrix.zero_empty, left_eq_add]
  rw [dotProduct, Finset.univ_eq_empty, Finset.sum_empty]

/-- The set of objective values attained by feasible vectors of the `0`--`1` linear program with
data `(c, A, b)`. -/
def objectiveValues
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    Set ℝ :=
  objectiveValue c '' feasibleSet c A b

/-- Membership in `objectiveValues c A b` means that some feasible binary vector attains the
value. -/
theorem mem_objectiveValues_iff
    {c : Fin n → ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    {r : ℝ} :
    r ∈ objectiveValues c A b ↔
      ∃ x : Fin n → ℝ, x ∈ feasibleSet c A b ∧ objectiveValue c x = r := by
  -- Membership in the source attained-value set is the witness form of image membership.
  rfl

/-- The canonical Chapter 1 MILP bridge for `(c, A, b)` is mixed `0,1`. -/
theorem toMixedIntegerLinearProgram_isMixedZeroOne
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    (toMixedIntegerLinearProgram c A b).IsMixedZeroOne := by
  -- Route correction: prove mixed-`0,1` status by feasible-set inclusion into the canonical
  -- mixed-`0,1` feasible set, normalizing the unique empty continuous block first.
  rw [MixedIntegerLinearProgram.isMixedZeroOne_iff_feasibleSet_subset_mixedZeroOneFeasibleSet]
  rintro ⟨x, y⟩ hxy
  have hy : y = fun i ↦ Fin.elim0 i := finZeroFunction_eq_elim0 y
  subst y
  have hsource : x ∈ feasibleSet c A b :=
    mem_toMixedIntegerLinearProgram_feasibleSet_iff.mp hxy
  rw [feasibleSet, Set.mem_setOf_eq] at hsource
  exact hsource

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_63/ZeroOneLinearProgram.lean

The source-facing attained-value set agrees with the objective-value set of the canonical
Chapter 1 MILP bridge. -/
theorem objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues
    (c : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) :
    objectiveValues c A b = (toMixedIntegerLinearProgram c A b).objectiveValues := by
  -- Transport attained-value witnesses back and forth across the canonical `Fin 0` embedding.
  ext r
  rw [mem_objectiveValues_iff,
    (toMixedIntegerLinearProgram c A b).mem_objectiveValues_iff]
  constructor
  · rintro ⟨x, hx, hobj⟩
    refine ⟨(x, fun i ↦ Fin.elim0 i), ?_, ?_⟩
    · exact mem_toMixedIntegerLinearProgram_feasibleSet_iff.mpr hx
    · calc
        (toMixedIntegerLinearProgram c A b).objectiveValue (x, fun i ↦ Fin.elim0 i) =
            objectiveValue c x := by
              symm
              exact objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
      _ = r := hobj
  · rintro ⟨⟨x, y⟩, hxy, hobj⟩
    have hy : y = fun i ↦ Fin.elim0 i := finZeroFunction_eq_elim0 y
    subst y
    have hsource : x ∈ feasibleSet c A b :=
      mem_toMixedIntegerLinearProgram_feasibleSet_iff.mp hxy
    refine ⟨x, hsource, ?_⟩
    calc
      objectiveValue c x =
          (toMixedIntegerLinearProgram c A b).objectiveValue (x, fun i ↦ Fin.elim0 i) :=
        objectiveValue_eq_toMixedIntegerLinearProgram_objectiveValue
      _ = r := hobj

#print axioms objectiveValues_eq_toMixedIntegerLinearProgram_objectiveValues

end ZeroOneLinearProgram
