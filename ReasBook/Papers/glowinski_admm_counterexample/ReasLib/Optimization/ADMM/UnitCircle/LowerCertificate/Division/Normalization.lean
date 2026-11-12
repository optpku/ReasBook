/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Arithmetic

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

/-- A structurally recursive merge with explicit fuel. Correctness is used
only when the fuel is at least the sum of the two input lengths. -/
def mergeTerms : ℕ → Laurent → Laurent → Laurent
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | n + 1, e :: p, f :: q =>
    if e.1 ≤ f.1 then e :: mergeTerms n p (f :: q)
      else f :: mergeTerms n (e :: p) q

theorem mergeTerms_perm (n : ℕ) (p q : Laurent) (hn : p.length + q.length ≤ n) :
    (mergeTerms n p q).Perm (p ++ q) := by
  induction n generalizing p q with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases p with
    | nil => simp only [mergeTerms, List.nil_append]; exact List.Perm.refl _
    | cons e p =>
      cases q with
      | nil => simp only [mergeTerms, List.append_nil]; exact List.Perm.refl _
      | cons f q =>
        simp only [mergeTerms]
        split_ifs with he
        · exact (ih p (f :: q) (by simp only [List.length_cons] at hn ⊢; omega)).cons e
        · exact ((ih (e :: p) q (by simp only [List.length_cons] at hn ⊢; omega)).cons f).trans
            List.perm_middle.symm

/-- Bounded-depth merge sorting remains a permutation at every fuel value.
The fixed fuel used for certificate data is checked by the resulting exact
normal-form equality, so no sorting hypothesis enters the semantic theorem. -/
def sortTerms : ℕ → Laurent → Laurent
  | 0, p => p
  | _ + 1, [] => []
  | _ + 1, [e] => [e]
  | n + 1, e :: f :: p =>
    let src := e :: f :: p
    let left := sortTerms n (src.take (src.length / 2))
    let right := sortTerms n (src.drop (src.length / 2))
    mergeTerms (left.length + right.length) left right

theorem sortTerms_perm (n : ℕ) (p : Laurent) : (sortTerms n p).Perm p := by
  induction n generalizing p with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases p with
    | nil => exact List.Perm.refl _
    | cons e p =>
      cases p with
      | nil => exact List.Perm.refl _
      | cons f p =>
        let src := e :: f :: p
        let l := src.take (src.length / 2)
        let r := src.drop (src.length / 2)
        change (mergeTerms ((sortTerms n l).length + (sortTerms n r).length)
          (sortTerms n l) (sortTerms n r)).Perm src
        have h := (mergeTerms_perm _ (sortTerms n l) (sortTerms n r) le_rfl).trans
          ((ih l).append (ih r))
        simpa only [l, r, List.take_append_drop] using h

/-- Adjacent equal exponents are combined, and zero coefficients are removed. -/
def combineHead (e : ℤ × ℚ) : Laurent → Laurent
  | [] => if e.2 = 0 then [] else [e]
  | f :: p =>
    if e.1 = f.1 then
      if e.2 + f.2 = 0 then p else (e.1, e.2 + f.2) :: p
    else if e.2 = 0 then f :: p else e :: f :: p

def collectTerms : Laurent → Laurent
  | [] => []
  | e :: p => combineHead e (collectTerms p)

theorem evaluate_combineHead (e : ℤ × ℚ) (p : Laurent) (z : ℂ) :
    evaluateLaurent (combineHead e p) z = (e.2 : ℂ) * z ^ e.1 + evaluateLaurent p z := by
  cases p with
  | nil =>
    simp only [combineHead]
    split_ifs with he <;> simp [he]
  | cons f p =>
    simp only [combineHead]
    split_ifs with hef he hef0
    · have heC : (e.2 : ℂ) + (f.2 : ℂ) = 0 := by exact_mod_cast he
      simp only [evaluateLaurent_cons, ← hef]
      linear_combination -z ^ e.1 * heC
    · simp only [evaluateLaurent_cons, Rat.cast_add, ← hef]
      ring
    · simp [hef0]
    · rfl

theorem evaluate_collectTerms (p : Laurent) (z : ℂ) :
    evaluateLaurent (collectTerms p) z = evaluateLaurent p z := by
  induction p with
  | nil => rfl
  | cons e p ih => rw [collectTerms, evaluate_combineHead, ih, evaluateLaurent_cons]

/-- Efficient exact normalization used by finite Laurent identities. -/
def normalForm (p : Laurent) : Laurent := collectTerms (sortTerms 14 p)

theorem evaluate_normalForm (p : Laurent) (z : ℂ) :
    evaluateLaurent (normalForm p) z = evaluateLaurent p z := by
  rw [normalForm, evaluate_collectTerms]
  exact ((sortTerms_perm 14 p).map (fun e : ℤ × ℚ ↦ (e.2 : ℂ) * z ^ e.1)).sum_eq

/-- Equality of checked finite normal forms gives exact complex evaluation. -/
theorem evaluate_eq_of_normalForm {p q : Laurent} (h : normalForm p = normalForm q) (z : ℂ) :
    evaluateLaurent p z = evaluateLaurent q z := by
  rw [← evaluate_normalForm p z, h, evaluate_normalForm]

end ADMM.UnitCircle.LowerCertificate.Division
