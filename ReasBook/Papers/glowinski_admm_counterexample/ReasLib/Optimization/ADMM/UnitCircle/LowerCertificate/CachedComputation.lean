/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerCertificate

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

/-- Balanced constant tables have logarithmic lookup depth in kernel reduction. -/
inductive LookupTree (α : Type)
  | leaf (value : α)
  | node (split : ℕ) (left right : LookupTree α)

def LookupTree.get {α : Type} : LookupTree α → ℕ → α
  | .leaf value, _ => value
  | .node split left right, k =>
      if k < split then left.get k else right.get (k - split)

/-- A finite factorial cache is certified by its defining recurrence. -/
def FactorialCacheValid (f : ℕ → ℕ) (N : ℕ) : Prop :=
  f 0 = 1 ∧ ∀ m : Fin N, f (m.val + 1) = (m.val + 1) * f m

instance (f : ℕ → ℕ) (N : ℕ) : Decidable (FactorialCacheValid f N) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem factorialCache_sound {f : ℕ → ℕ} {N : ℕ} (h : FactorialCacheValid f N)
    {m : ℕ} (hm : m ≤ N) : f m = Nat.factorial m := by
  induction m with
  | zero => exact h.1
  | succ m ih =>
    rw [h.2 ⟨m, by omega⟩, Nat.factorial_succ, ih (by omega)]

/-- Factorial quotient with a checked cache; the fallback makes its semantic
identity valid for every argument, beyond the finite cached region as well. -/
def cachedChoose (f : ℕ → ℕ) (N n k : ℕ) : ℕ :=
  if n ≤ N then if k ≤ n then f n / (f k * f (n - k)) else 0
  else Nat.fast_choose n k

theorem cachedChoose_sound {f : ℕ → ℕ} {N : ℕ} (h : FactorialCacheValid f N)
    (n k : ℕ) : cachedChoose f N n k = Nat.fast_choose n k := by
  unfold cachedChoose
  split_ifs with hn hk
  · rw [factorialCache_sound h hn, factorialCache_sound h (hk.trans hn),
      factorialCache_sound h ((Nat.sub_le n k).trans hn),
      ← Nat.choose_eq_factorial_div_factorial hk, Nat.choose_eq_fast_choose]
  · rw [← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt (by omega)]
  · rfl

namespace IntegerCoefficients

def basisWith (choose : ℕ → ℕ → ℕ) (n k : ℕ) : List ℤ :=
  List.replicate k 0 ++ List.ofFn (fun j : Fin (n - k + 1) ↦
    (choose n k : ℤ) * choose (n - k) j * (-1) ^ (j : ℕ))

def expansionWith (choose : ℕ → ℕ → ℕ) (n : ℕ) (c : Fin (n + 1) → ℤ) : List ℤ :=
  sum (List.ofFn (fun k : Fin (n + 1) ↦ scale (c k) (basisWith choose n k)))

def affineWith (choose : ℕ → ℕ → ℕ) (n : ℕ) (p : Fin (n + 1) → ℤ)
    (A B S : ℤ) : List ℤ :=
  List.ofFn (fun j : Fin (n + 1) ↦ ∑ k : Fin (n + 1),
    if (j : ℕ) ≤ (k : ℕ) then
      p k * (choose k j : ℤ) * A ^ ((k : ℕ) - j) * B ^ (j : ℕ) * S ^ (n - k)
    else 0)

theorem expansionWith_sound (choose : ℕ → ℕ → ℕ)
    (h : ∀ n k, choose n k = Nat.fast_choose n k) (n : ℕ) (c : Fin (n + 1) → ℤ) :
    expansionWith choose n c = expansion n c := by
  simp only [expansionWith, expansion, basisWith, basis, h]

theorem affineWith_sound (choose : ℕ → ℕ → ℕ)
    (h : ∀ n k, choose n k = Nat.fast_choose n k) (n : ℕ)
    (p : Fin (n + 1) → ℤ) (A B S : ℤ) :
    affineWith choose n p A B S = affine n p A B S := by
  simp only [affineWith, affine, h]

end IntegerCoefficients

end ADMM.UnitCircle.LowerCertificate
