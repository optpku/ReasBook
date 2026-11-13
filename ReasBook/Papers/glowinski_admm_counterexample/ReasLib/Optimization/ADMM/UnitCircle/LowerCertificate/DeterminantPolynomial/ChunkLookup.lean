/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.CachedComputation
public import Mathlib.Data.List.GetD

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

/-- A balanced tree references the original short input chunks directly. -/
def flattenChunks {α : Type} : LookupTree (List α) → List α
  | .leaf xs => xs
  | .node _ left right => flattenChunks left ++ flattenChunks right

def validChunks {α : Type} : LookupTree (List α) → Prop
  | .leaf xs => xs.length ≤ 32
  | .node split left right =>
      (flattenChunks left).length = 32 * split ∧ validChunks left ∧ validChunks right

def validChunksDecidable {α : Type} :
    (t : LookupTree (List α)) → Decidable (validChunks t)
  | .leaf xs => inferInstanceAs (Decidable (xs.length ≤ 32))
  | .node split left right =>
    letI := validChunksDecidable left
    letI := validChunksDecidable right
    inferInstanceAs (Decidable
      ((flattenChunks left).length = 32 * split ∧ validChunks left ∧ validChunks right))

instance {α : Type} (t : LookupTree (List α)) : Decidable (validChunks t) :=
  validChunksDecidable t

def chunkLookup {α : Type} (t : LookupTree (List α)) (i : ℕ) (fallback : α) : α :=
  (t.get (i / 32)).getD (i % 32) fallback

/-- Valid short-chunk lookup returns precisely the original flattened vector.
The certificate therefore changes lookup cost, rather than mathematical data. -/
theorem chunkLookup_eq_getD {α : Type} (t : LookupTree (List α))
    (ht : validChunks t) (i : ℕ) (hi : i < (flattenChunks t).length) (fallback : α) :
    chunkLookup t i fallback = (flattenChunks t).getD i fallback := by
  induction t generalizing i with
  | leaf xs =>
    have hlen : xs.length ≤ 32 := ht
    have him : i % 32 = i := Nat.mod_eq_of_lt (by change i < xs.length at hi; omega)
    simpa only [chunkLookup, LookupTree.get, flattenChunks, him]
  | node split left right ihl ihr =>
    obtain ⟨hlen, hleft, hright⟩ := ht
    change i < (flattenChunks left ++ flattenChunks right).length at hi
    rw [List.length_append] at hi
    by_cases hilt : i < (flattenChunks left).length
    · have hsplit : i / 32 < split := by omega
      change (if i / 32 < split then left.get (i / 32)
        else right.get (i / 32 - split)).getD (i % 32) fallback = _
      rw [if_pos hsplit]
      change chunkLookup left i fallback =
        (flattenChunks left ++ flattenChunks right).getD i fallback
      rw [ihl hleft i hilt]
      exact (List.getD_append _ _ fallback i hilt).symm
    · have hile : (flattenChunks left).length ≤ i := by omega
      have hsplit : ¬ i / 32 < split := by omega
      have hbound : i - (flattenChunks left).length < (flattenChunks right).length := by omega
      have hdiv : (i - (flattenChunks left).length) / 32 = i / 32 - split := by omega
      have hmod : (i - (flattenChunks left).length) % 32 = i % 32 := by omega
      change (if i / 32 < split then left.get (i / 32)
        else right.get (i / 32 - split)).getD (i % 32) fallback = _
      rw [if_neg hsplit, ← hdiv, ← hmod]
      change chunkLookup right (i - (flattenChunks left).length) fallback =
        (flattenChunks left ++ flattenChunks right).getD i fallback
      rw [ihr hright _ hbound]
      exact (List.getD_append_right _ _ fallback i hile).symm

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
