/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.ChunkLookup
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.IntegerLaurent
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.ChebyshevTransform

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

set_option maxRecDepth 8192

def windowIndices (n : ℕ) : List ℤ :=
  List.ofFn (fun i : Fin (2 * n + 1) ↦ (i.val : ℤ) - n)

def pairedIndices (n : ℕ) : List ℤ :=
  0 :: (List.ofFn (fun i : Fin n ↦ [(i.val + 1 : ℤ), -(i.val + 1 : ℤ)])).flatten

def indexedTerm (n : ℕ) (D : ℤ) (c : ℕ → ℤ) (j : ℤ) : ℤ × ℚ :=
  (j, (c (j + n).toNat : ℚ) / D)

theorem window_map (n : ℕ) (D : ℤ) (c : ℕ → ℤ) :
    (windowIndices n).map (indexedTerm n D c) =
      List.ofFn (fun i : Fin (2 * n + 1) ↦
        ((i.val : ℤ) - n, (c i : ℚ) / D)) := by
  simp only [windowIndices, List.map_ofFn, Function.comp_def, indexedTerm,
    sub_add_cancel, Int.toNat_natCast]

theorem paired_map (n : ℕ) (D : ℤ) (c : ℕ → ℤ) :
    (pairedIndices n).map (indexedTerm n D c) =
      pairedLaurent n ((c n : ℚ) / D)
        (fun i ↦ (c (i.val + n + 1) : ℚ) / D)
        (fun i ↦ (c (n - 1 - i.val) : ℚ) / D) := by
  simp only [pairedIndices, pairedLaurent, List.map_cons, indexedTerm,
    zero_add, Int.toNat_natCast, List.map_flatten, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  have hp : (i.val + 1 : ℤ) + n = ((i.val + n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have hm : -(i.val + 1 : ℤ) + n = ((n - 1 - i.val : ℕ) : ℤ) := by
    have hi := i.isLt
    omega
  simp only [List.map_cons, List.map_nil, indexedTerm, hp, hm, Int.toNat_natCast]

theorem list_eq_ofFn_lookup (p : List ℤ) (n : ℕ) (hp : p.length = n)
    (c : ℕ → ℤ) (hc : ∀ i < n, p.getD i 0 = c i) :
    p = List.ofFn (fun i : Fin n ↦ c i) := by
  apply List.ext_getElem (hp.trans (List.length_ofFn).symm)
  intro i hip hiq
  rw [List.getElem_ofFn, List.getElem_eq_getD 0]
  exact hc i (by omega)

theorem rationalLaurent_ofFn (n : ℕ) (offset D : ℤ) (c : Fin n → ℤ) :
    Determinant.rationalLaurent offset D (List.ofFn c) =
      List.ofFn (fun i : Fin n ↦ (offset + (i.val : ℤ), (c i : ℚ) / D)) := by
  induction n generalizing offset with
  | zero => simp [Determinant.rationalLaurent]
  | succ n ih =>
    rw [List.ofFn_succ, Determinant.rationalLaurent, List.ofFn_succ]
    simp only [Fin.val_zero, Int.natCast_zero, add_zero]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ, Int.natCast_add, Int.natCast_one]
    congr 1
    ring

/-- Dense integer source vectors are regrouped into positive/negative pairs.
Only the finite index permutation is checked computationally; source numerators
are retained through the proved lookup representation. -/
theorem rationalLaurent_pairing (n : ℕ) (D : ℤ) (p : List ℤ)
    (hp : p.length = 2 * n + 1) (c : ℕ → ℤ)
    (hc : ∀ i < 2 * n + 1, p.getD i 0 = c i)
    (hperm : (windowIndices n).Perm (pairedIndices n)) :
    (Determinant.rationalLaurent (-(n : ℤ)) D p).Perm
      (pairedLaurent n ((c n : ℚ) / D)
        (fun i ↦ (c (i.val + n + 1) : ℚ) / D)
        (fun i ↦ (c (n - 1 - i.val) : ℚ) / D)) := by
  rw [list_eq_ofFn_lookup p (2 * n + 1) hp c hc, rationalLaurent_ofFn]
  have hd : (List.ofFn (fun i : Fin (2 * n + 1) ↦
      (-(n : ℤ) + (i.val : ℤ), (c i : ℚ) / D))) =
        (windowIndices n).map (indexedTerm n D c) := by
    rw [window_map]
    congr 1
    funext i
    congr 1
    ring
  rw [hd, ← paired_map]
  exact hperm.map (indexedTerm n D c)

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
