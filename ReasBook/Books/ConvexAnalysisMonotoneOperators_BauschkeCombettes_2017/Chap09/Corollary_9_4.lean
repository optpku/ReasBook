/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

/-- For a family of extended-real-valued functions, `nonemptyFinitePartialSums f x` is the set of
all finite nonempty partial sums of the values `f i x`. -/
def nonemptyFinitePartialSums (f : I → H → EReal) (x : H) : Set EReal :=
  Set.range
    (fun J : {s : Finset I // s.Nonempty} ↦ Finset.sum (J : Finset I) (fun i ↦ f i x))

/-- The source-defined sum of a family in `Γ(ℋ)`: use the ordinary finite sum when `I` is finite,
and otherwise take the supremum of the nonempty finite partial sums pointwise. -/
noncomputable def familySum (f : I → H → EReal) : H → EReal :=
  by
    classical
    exact
      if hI : Finite I then
        let _ : Finite I := hI
        let _ : Fintype I := Fintype.ofFinite I
        fun x ↦ ∑ i, f i x
      else
        fun x ↦ sSup (nonemptyFinitePartialSums f x)

-- Proof sketch: unfold `familySum`; in the infinite branch the defining `if` reduces directly to
-- the supremum of the nonempty finite partial sums.
/-- For an infinite index type, `familySum` is the pointwise supremum of the nonempty finite
partial sums. -/
theorem familySum_of_infinite (f : I → H → EReal) (hI : ¬ Finite I) :
    familySum f = fun x ↦ sSup (nonemptyFinitePartialSums f x) := by
  -- The infinite branch of the defining `if` is selected directly.
  classical
  unfold familySum
  by_cases h : Finite I
  · exact (hI h).elim
  · simp [h]

-- Proof sketch: unfold `familySum`; in the finite branch the defining `if` reduces to the usual
-- sum over the canonical `Fintype` structure attached to `I`.
/-- For a finite index type, `familySum` is the usual finite pointwise sum. -/
theorem familySum_of_finite (f : I → H → EReal) [Finite I] :
    familySum f = (let _ : Fintype I := Fintype.ofFinite I; fun x ↦ ∑ i, f i x) := by
  -- The finite branch of the defining `if` is selected directly.
  classical
  unfold familySum
  by_cases h : Finite I
  · simp [h]
  · exact (h inferInstance).elim

/-- Helper for Corollary 9.4: the pointwise sum of two Jensen-convex extended-real-valued
functions is Jensen-convex. -/
lemma isConvex_add {g h : H → EReal} (hg : IsConvex g) (hh : IsConvex h) :
    IsConvex (fun x ↦ g x + h x) := by
  intro x y a ha0 ha1
  have haE_nonneg : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha0
  have hbE_nonneg : (0 : EReal) ≤ (1 - a : EReal) := by
    exact_mod_cast sub_nonneg.mpr ha1
  have haE_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
  have hbE_ne_top : (1 - a : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - a)
  -- Add the two Jensen inequalities and then regroup the weighted terms.
  calc
    g (a • x + (1 - a) • y) + h (a • x + (1 - a) • y)
        ≤ ((a : EReal) * g x + (1 - a : EReal) * g y) +
            ((a : EReal) * h x + (1 - a : EReal) * h y) := by
          exact add_le_add (hg ha0 ha1) (hh ha0 ha1)
    _ = (a : EReal) * (g x + h x) + (1 - a : EReal) * (g y + h y) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top,
            EReal.left_distrib_of_nonneg_of_ne_top hbE_nonneg hbE_ne_top]
          simp [mul_comm, add_assoc, add_left_comm]

/-- Helper for Corollary 9.4: the sum of two lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
lemma lowerSemicontinuous_add_ereal {g h : H → EReal} (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  -- Compare the pointwise sum with the liminf of each summand separately.
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using (EReal.le_liminf_add :
        Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
          Filter.liminf (g + h) (nhds x))

/-- Helper for Corollary 9.4: a finite sum of lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
lemma lowerSemicontinuous_finset_sum_ereal (f : I → H → EReal) (s : Finset I)
    (hf : ∀ i ∈ s, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x ↦ Finset.sum s (fun i ↦ f i x)) := by
  classical
  -- Induct on the finite index set, using lower semicontinuity of pointwise addition.
  induction s using Finset.induction_on with
  | empty =>
      simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (0 : EReal)))
  | @insert i s hi ih =>
      have hi_term : LowerSemicontinuous (f i) := hf i (Finset.mem_insert_self i s)
      have hs_sum : LowerSemicontinuous (fun x ↦ Finset.sum s (fun j ↦ f j x)) :=
        ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      -- Add the new term to the already lower semicontinuous smaller partial sum.
      simpa [Finset.sum_insert, hi] using lowerSemicontinuous_add_ereal hi_term hs_sum

/-- Helper for Corollary 9.4: every finite pointwise partial sum of members of `Γ(ℋ)` again lies in
`Γ(ℋ)`. -/
lemma finset_sum_mem_gamma (f : I → H → EReal) (s : Finset I) (hf : ∀ i, f i ∈ gamma H) :
    (fun x ↦ Finset.sum s (fun i ↦ f i x)) ∈ gamma H := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · classical
    -- Induct on the finite index set, using stability of Jensen convexity under pointwise
    -- addition.
    induction s using Finset.induction_on with
    | empty =>
        intro x y a ha0 ha1
        simp
    | @insert i s hi ih =>
        have hfi : IsConvex (f i) := (mem_gamma_iff (f i)).mp (hf i) |>.1
        -- The inductive partial sum is already convex, so add the new term on top.
        simpa [Finset.sum_insert, hi] using isConvex_add hfi ih
  · classical
    have hterm : ∀ i, LowerSemicontinuous (f i) := fun i ↦ (mem_gamma_iff (f i)).mp (hf i) |>.2
    -- Lower semicontinuity is preserved under finite pointwise sums.
    exact lowerSemicontinuous_finset_sum_ereal f s (fun i hi ↦ hterm i)

/-- Helper for Corollary 9.4: for an infinite index type, `familySum` is the indexed supremum of
its nonempty finite partial sums. -/
lemma familySum_eq_iSup_nonemptyFinitePartialSums (f : I → H → EReal) (hI : ¬ Finite I) :
    familySum f = fun x ↦ ⨆ J : {s : Finset I // s.Nonempty}, Finset.sum (J : Finset I) (fun i ↦ f i x) := by
  -- Rewrite the defining `sSup` as an indexed supremum over the subtype of nonempty finite sets.
  rw [familySum_of_infinite f hI]
  ext x
  rw [nonemptyFinitePartialSums, sSup_range]

/-- Helper for Corollary 9.4: a weighted pointwise supremum is bounded by the corresponding
weighted sum of the separate suprema when the weights are nonnegative. -/
lemma weighted_iSup_le_weighted_iSup_cor94 {J : Type*} {u v : J → EReal} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (⨆ j, (a : EReal) * u j + (b : EReal) * v j) ≤
      (a : EReal) * (⨆ j, u j) + (b : EReal) * (⨆ j, v j) := by
  have haE : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hbE : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  -- Bound each weighted supremum termwise by the corresponding weighted global supremum.
  have hu : (⨆ j, (a : EReal) * u j) ≤ (a : EReal) * (⨆ j, u j) := by
    refine iSup_le fun j ↦ ?_
    exact mul_le_mul_of_nonneg_left (le_iSup u j) haE
  have hv : (⨆ j, (b : EReal) * v j) ≤ (b : EReal) * (⨆ j, v j) := by
    refine iSup_le fun j ↦ ?_
    exact mul_le_mul_of_nonneg_left (le_iSup v j) hbE
  -- The supremum of sums is controlled by the sum of the separate suprema.
  calc
    (⨆ j, (a : EReal) * u j + (b : EReal) * v j)
        ≤ (⨆ j, (a : EReal) * u j) + ⨆ j, (b : EReal) * v j := EReal.iSup_add_le_add_iSup
    _ ≤ (a : EReal) * (⨆ j, u j) + (b : EReal) * (⨆ j, v j) := add_le_add hu hv

/-- Helper for Corollary 9.4: the pointwise supremum of Jensen-convex extended-real-valued
functions is Jensen-convex. -/
lemma isConvex_iSup_of_isConvex_cor94 {J : Type*} (f : J → H → EReal)
    (hf : ∀ j, IsConvex (f j)) :
    IsConvex (fun x ↦ ⨆ j, f j x) := by
  intro x y a ha0 ha1
  have hpointwise :
      (⨆ j, f j (a • x + (1 - a) • y)) ≤
        ⨆ j, (a : EReal) * f j x + (1 - a : EReal) * f j y := by
    refine iSup_le fun j ↦ ?_
    exact (hf j ha0 ha1).trans
      (le_iSup (fun j ↦ (a : EReal) * f j x + (1 - a : EReal) * f j y) j)
  have hone_sub : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  -- Apply the weighted supremum estimate to match the Jensen bound for the supremum.
  calc
    (⨆ j, f j (a • x + (1 - a) • y))
        ≤ ⨆ j, (a : EReal) * f j x + (1 - a : EReal) * f j y := hpointwise
    _ ≤ (a : EReal) * (⨆ j, f j x) + (1 - a : EReal) * (⨆ j, f j y) :=
      weighted_iSup_le_weighted_iSup_cor94 ha0 hone_sub

/-- Helper for Corollary 9.4: the pointwise supremum of a family in `Γ(ℋ)` is lower
semicontinuous. -/
lemma lowerSemicontinuous_iSup_of_mem_gamma_cor94 {J : Type*} (f : J → H → EReal)
    (hf : ∀ j, f j ∈ gamma H) :
    LowerSemicontinuous (fun x ↦ ⨆ j, f j x) := by
  -- Extract lower semicontinuity from each `gamma` hypothesis and pass to the supremum.
  refine lowerSemicontinuous_iSup fun j ↦ ?_
  exact (mem_gamma_iff (f j)).mp (hf j) |>.2

-- Proof sketch: in case (i), reduce `familySum` to the ordinary finite sum and apply the finite
-- stability of convexity and lower semicontinuity under pointwise addition. In case (ii), for each
-- nonempty finite subset `J`, the partial sum belongs to `Γ(ℋ)` by the finite case; the
-- nonnegativity hypothesis makes these partial sums monotone in `J`, so `familySum` is their
-- pointwise supremum and Proposition 9.3 applies.
/-- Corollary 9.4: if `(fᵢ)ᵢ` is a family in `Γ(ℋ)`, then the source-defined pointwise sum
`familySum f` again belongs to `Γ(ℋ)` whenever either (i) `I` is finite and no `fᵢ` attains
`-∞`, or (ii) every `fᵢ` is pointwise nonnegative. -/
theorem familySum_mem_gamma
    (f : I → H → EReal) (hf : ∀ i, f i ∈ gamma H)
    (hcases : (Finite I ∧ ∀ i x, f i x ≠ ⊥) ∨ ∀ i x, (0 : EReal) ≤ f i x) :
    familySum f ∈ gamma H := by
  classical
  by_cases hI : Finite I
  · let _ : Finite I := hI
    let _ : Fintype I := Fintype.ofFinite I
    have hsum : (fun x ↦ ∑ i, f i x) ∈ gamma H := by
      -- In the finite branch, `familySum` is the ordinary finite sum over `I`.
      simpa using finset_sum_mem_gamma f (Finset.univ : Finset I) hf
    rw [familySum_of_finite f]
    simpa using hsum
  · -- In the infinite branch, rewrite `familySum` as the supremum of its finite partial sums.
    rw [familySum_eq_iSup_nonemptyFinitePartialSums f hI, mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · -- Each nonempty finite partial sum is convex, so their pointwise supremum is convex.
      exact isConvex_iSup_of_isConvex_cor94 (J := {s : Finset I // s.Nonempty})
        (fun J x ↦ Finset.sum (J : Finset I) (fun i ↦ f i x))
        (fun J ↦ (mem_gamma_iff _).mp (finset_sum_mem_gamma f (J : Finset I) hf) |>.1)
    · -- Each nonempty finite partial sum is lower semicontinuous, so their supremum is too.
      exact lowerSemicontinuous_iSup_of_mem_gamma_cor94 (J := {s : Finset I // s.Nonempty})
        (fun J x ↦ Finset.sum (J : Finset I) (fun i ↦ f i x))
        (fun J ↦ finset_sum_mem_gamma f (J : Finset I) hf)

end ERealFunction
