/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramBounds

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open Period1024
open scoped RealInnerProductSpace

/-- A flattened block index denotes an actual vector of the Fourier orbit. -/
noncomputable def orbitVertex (i : ℕ) : Ambient :=
  gramFamily (decide (1024 ≤ i)) (i : Phase)

/-- The integer circulant index agrees with subtraction in the cyclic group. -/
theorem phase_difference_val (i j : ℕ) :
    ((j : Phase) - (i : Phase)).val =
      (j % 1024 + 1024 - i % 1024) % 1024 := by
  change ((j : ZMod 1024) - (i : ZMod 1024)).val = _
  have hi : i % 1024 ≤ j % 1024 + 1024 := by
    have := Nat.mod_lt i (by decide : 0 < 1024)
    omega
  have heq : ((j % 1024 + 1024 - i % 1024 : ℕ) : ZMod 1024) =
      (j : ZMod 1024) - (i : ZMod 1024) := by
    rw [Nat.cast_sub hi, Nat.cast_add]
    simp only [ZMod.natCast_mod, ZMod.natCast_self, add_zero]
  have hv := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast, ADMM.RefinedEndpoint.Data.period] using hv.symm

/-- Each flattened Gram entry encloses the corresponding actual inner product. -/
theorem gramEntryNumerator_contains (i j : ℕ) :
    ((gramEntryNumerator i j).toRat gramDenominator).Contains
      (inner ℝ (orbitVertex i) (orbitVertex j)) := by
  simpa only [orbitVertex, gramEntryNumerator, phase_difference_val] using
    gramNumerator_contains (decide (1024 ≤ i)) (decide (1024 ≤ j))
      (i : Phase) (j : Phase)

/-- Interpret a sparse integer list as a real linear combination of orbit vectors. -/
noncomputable def sparseValue (A : SparseVector) : Ambient :=
  (A.map fun a ↦ (a.2 : ℝ) • orbitVertex a.1).sum

theorem sparseValue_nil : sparseValue [] = 0 := rfl

theorem sparseValue_cons (a : ℕ × ℤ) (A : SparseVector) :
    sparseValue (a :: A) = (a.2 : ℝ) • orbitVertex a.1 + sparseValue A := rfl

theorem inner_sparseValue_right (x : Ambient) (B : SparseVector) :
    inner ℝ x (sparseValue B) =
      (B.map fun b ↦ (b.2 : ℝ) * inner ℝ x (orbitVertex b.1)).sum := by
  induction B with
  | nil => simp [sparseValue]
  | cons b B ih =>
    simp only [sparseValue_cons, inner_add_right, real_inner_smul_right,
      List.map_cons, List.sum_cons, ih]

theorem sparseValue_inner (A B : SparseVector) :
    inner ℝ (sparseValue A) (sparseValue B) =
      (A.map fun a ↦ (B.map fun b ↦
        ((a.2 * b.2 : ℤ) : ℝ) * inner ℝ (orbitVertex a.1) (orbitVertex b.1)).sum).sum := by
  induction A with
  | nil => simp [sparseValue]
  | cons a A ih =>
    simp only [sparseValue_cons, inner_add_left, real_inner_smul_left,
      List.map_cons, List.sum_cons, ih, inner_sparseValue_right]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro b _
    push_cast
    ring

/-- The sparse integer pairing is sound for the actual Fourier orbit. -/
theorem pairNumerator_contains (A B : SparseVector) :
    ((pairNumerator A B).toRat gramDenominator).Contains
      (inner ℝ (sparseValue A) (sparseValue B)) := by
  rw [sparseValue_inner]
  exact IntInterval.contains_sum_map A _ _ _ (fun a _ ↦
    IntInterval.contains_sum_map B _ _ _ (fun b _ ↦
      IntInterval.contains_scale (gramEntryNumerator_contains a.1 b.1) (a.2 * b.2)))

end ConsensusADMM.RefinedEndpoint.Certificate
