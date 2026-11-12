/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.ChunkLookup

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

def flattenElements {α : Type} : LookupTree α → List α
  | .leaf a => [a]
  | .node _ left right => flattenElements left ++ flattenElements right

def validElements {α : Type} : LookupTree α → Prop
  | .leaf _ => True
  | .node split left right =>
      (flattenElements left).length = split ∧ validElements left ∧ validElements right

def validElementsDecidable {α : Type} : (t : LookupTree α) → Decidable (validElements t)
  | .leaf _ => inferInstanceAs (Decidable True)
  | .node split left right =>
    letI := validElementsDecidable left
    letI := validElementsDecidable right
    inferInstanceAs (Decidable
      ((flattenElements left).length = split ∧ validElements left ∧ validElements right))

instance {α : Type} (t : LookupTree α) : Decidable (validElements t) :=
  validElementsDecidable t

theorem elementLookup_eq_getD {α : Type} (t : LookupTree α) (ht : validElements t)
    (i : ℕ) (hi : i < (flattenElements t).length) (fallback : α) :
    t.get i = (flattenElements t).getD i fallback := by
  induction t generalizing i with
  | leaf a =>
    have hi0 : i = 0 := by change i < 1 at hi; omega
    simp only [hi0, LookupTree.get, flattenElements, List.getD_cons_zero]
  | node split left right ihl ihr =>
    obtain ⟨hlen, hl, hr⟩ := ht
    change i < (flattenElements left ++ flattenElements right).length at hi
    rw [List.length_append] at hi
    change (if i < split then left.get i else right.get (i - split)) =
      (flattenElements left ++ flattenElements right).getD i fallback
    by_cases hleft : i < (flattenElements left).length
    · rw [if_pos (by omega), ihl hl i hleft]
      exact (List.getD_append _ _ fallback i hleft).symm
    · have hright : (flattenElements left).length ≤ i := by omega
      rw [if_neg (by omega), ← hlen]
      rw [ihr hr _ (by omega)]
      exact (List.getD_append_right _ _ fallback i hright).symm

structure CoefficientRow where
  size : ℕ
  values : LookupTree ℤ

def CoefficientRow.coefficient (row : CoefficientRow) (j : ℕ) : ℤ :=
  if j < row.size then row.values.get j else 0

def RowRepresents (row : CoefficientRow) (p : List ℤ) : Prop :=
  validElements row.values ∧ flattenElements row.values = p ∧ row.size = p.length

theorem row_coefficient_correct (row : CoefficientRow) (p : List ℤ)
    (h : RowRepresents row p) (j : ℕ) : row.coefficient j = p.getD j 0 := by
  unfold CoefficientRow.coefficient
  by_cases hj : j < row.size
  · rw [if_pos hj, elementLookup_eq_getD row.values h.1 j
      (by rw [h.2.1, ← h.2.2]; exact hj), h.2.1]
  · rw [if_neg hj]
    exact (List.getD_eq_default p 0 (by rw [← h.2.2]; omega)).symm

inductive RowsRepresent : LookupTree CoefficientRow → LookupTree (List ℤ) → Prop
  | leaf (row : CoefficientRow) (p : List ℤ) (h : RowRepresents row p) :
      RowsRepresent (.leaf row) (.leaf p)
  | node (split : ℕ) {rowsL rowsR : LookupTree CoefficientRow}
      {sourceL sourceR : LookupTree (List ℤ)}
      (hL : RowsRepresent rowsL sourceL) (hR : RowsRepresent rowsR sourceR) :
      RowsRepresent (.node split rowsL rowsR) (.node split sourceL sourceR)

theorem rowLookup_correct {rows : LookupTree CoefficientRow}
    {source : LookupTree (List ℤ)} (h : RowsRepresent rows source) (i j : ℕ) :
    (rows.get i).coefficient j = (source.get i).getD j 0 := by
  induction h generalizing i with
  | leaf row p h => exact row_coefficient_correct row p h j
  | node split hL hR ihL ihR =>
    simp only [LookupTree.get]
    split_ifs with hi
    · exact ihL i
    · exact ihR (i - split)

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
