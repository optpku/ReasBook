/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_71

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)
open scoped BigOperators

noncomputable section

section

local notation "E" => EuclideanSpace ℝ (Fin 4)
local notation "x₀" => (!₂[2, 3, -2, 1] : E)
local notation "y₀" => (!₂[2, 3, 0, 0] : E)
local notation "z₀" => (!₂[0, 3, -2, 0] : E)

/- Example 6.72 is `source-facing`: the canonical owner abstractions for this item are the
set-valued projection map `P[...]` from `Lemma_6_71` and the sparse-vector set `C_[s]` from
`Definition_6_12`. Since the textbook content is a concrete worked projection computation, the
main labeled entry should remain the explicit equality for this specific vector rather than a new
wrapper around the general characterization from Lemma 6.71. -/

/-- Helper for Example 6.72: the sum of the two largest absolute coordinates of `x₀` is `5`. -/
private theorem sum_k_largest_abs_two_example :
    sum_k_largest_abs 2 x₀ = 5 := by
  let σ : Equiv.Perm (Fin 4) := by
    simpa using (Fintype.equivFin (Fin 4)).symm
  let f : Fin 4 → ℝ := fun i ↦
    (toLp 2 fun j : Fin 4 ↦ |x₀ j|) i
  -- Compute the absolute-value multiset explicitly and sort it in descending order.
  unfold sum_k_largest_abs sum_of_k_largest_values
  change (((List.ofFn (f ∘ σ)).mergeSort (· ≥ ·)).take 2).sum = 5
  have hperm : List.Perm (List.ofFn (f ∘ σ)) [2, 3, 2, 1] := by
    have hσ : List.Perm (List.ofFn (f ∘ σ)) (List.ofFn f) := Equiv.Perm.ofFn_comp_perm σ f
    have hf : [f 0, f 1, f 2, f 3] = ([2, 3, 2, 1] : List ℝ) := by
      simp [f]
    simpa [List.ofFn_succ', List.ofFn_succ, List.ofFn_zero, hf] using hσ
  have hsort : (List.ofFn (f ∘ σ)).mergeSort (· ≥ ·) = [3, 2, 2, 1] := by
    have hperm' : List.Perm ((List.ofFn (f ∘ σ)).mergeSort (· ≥ ·)) [3, 2, 2, 1] :=
      (List.mergeSort_perm (List.ofFn (f ∘ σ)) _).trans <| hperm.trans <|
        (List.Perm.swap (2 : ℝ) 3 [2, 1]).symm
    exact hperm'.eq_of_pairwise'
      (by simpa using List.pairwise_mergeSort' (· ≥ ·) (List.ofFn (f ∘ σ)))
      (by norm_num)
  rw [hsort]
  norm_num

/-- Helper for Example 6.72: the size-`2` supports maximizing the absolute-value sum are exactly
`{0, 1}` and `{1, 2}`. -/
private theorem top_supports_two_example (S : Finset (Fin 4))
    (hS : S.card = 2 ∧
      S.sum (fun i ↦ |x₀ i|) = 5) :
    S = ({0, 1} : Finset (Fin 4)) ∨ S = {1, 2} := by
  -- There are only finitely many supports in `Fin 4`, so a direct case split is stable here.
  fin_cases S <;> simp at hS ⊢ <;> first | aesop | norm_num at hS

-- Proof sketch: apply `projection_mapping_sSparseVectors_eq_top_abs_coordinate_projections` with
-- `n = 4`, `s = 2`, and `x = (2, 3, -2, 1)`. The two largest absolute values are `3` and `2`,
-- with a tie between the first and third coordinates for the second slot, so the maximizing
-- supports are exactly `{0, 1}` and `{1, 2}`; evaluating `(↑S : Set (Fin 4)).indicator x` on
-- those supports gives the two displayed vectors.
/-- Example 6.72: when `n = 4`, the projection of `(2, 3, -2, 1)^T` onto the set `C_2` of
`2`-sparse vectors consists exactly of the two vectors obtained by keeping the coordinates
indexed by `{0, 1}` or `{1, 2}` and zeroing out the others. -/
theorem projection_mapping_sSparseVectors_two_example_eq_two_point_set :
    P[toLp 2 '' C_[2]] !₂[(2 : ℝ), 3, -2, 1] =
      {!₂[(2 : ℝ), 3, 0, 0], !₂[(0 : ℝ), 3, -2, 0]} := by
  change P[toLp 2 '' C_[2]] x₀ = {y₀, z₀}
  -- Rewrite the projection set using the support-maximization characterization from Lemma 6.71.
  rw [projection_mapping_sSparseVectors_eq_top_abs_coordinate_projections
    (by decide) x₀]
  ext y
  constructor
  · rintro ⟨S, hS, rfl⟩
    -- Replace the abstract objective value by the concrete top-two absolute-value sum.
    have hS' : S.card = 2 ∧ S.sum (fun i ↦ |x₀ i|) = 5 := by
      rwa [sum_k_largest_abs_two_example] at hS
    rcases top_supports_two_example S hS' with rfl | rfl
    · left
      ext i
      fin_cases i <;> simp
    · right
      ext i
      fin_cases i <;> simp
  · intro hy
    -- Each displayed vector comes from one of the two maximizing supports.
    rcases hy with rfl | rfl
    · refine ⟨({0, 1} : Finset (Fin 4)), ?_⟩
      refine ⟨?_, ?_⟩
      · constructor
        · decide
        · simp [sum_k_largest_abs_two_example]
          norm_num
      · ext i
        fin_cases i <;> simp
    · refine ⟨({1, 2} : Finset (Fin 4)), ?_⟩
      refine ⟨?_, ?_⟩
      · constructor
        · decide
        · simp [sum_k_largest_abs_two_example]
          norm_num
      · ext i
        fin_cases i <;> simp

end
