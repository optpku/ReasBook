/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.CachedComputation

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

def PowerCacheValid (f : ℕ → ℤ) (a : ℤ) (N : ℕ) : Prop :=
  f 0 = 1 ∧ ∀ m : Fin N, f (m.val + 1) = f m * a

instance (f : ℕ → ℤ) (a : ℤ) (N : ℕ) : Decidable (PowerCacheValid f a N) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem powerCache_sound {f : ℕ → ℤ} {a : ℤ} {N : ℕ} (h : PowerCacheValid f a N)
    {m : ℕ} (hm : m ≤ N) : f m = a ^ m := by
  induction m with
  | zero => simpa using h.1
  | succ m ih => rw [h.2 ⟨m, by omega⟩, pow_succ, ih (by omega)]

def cachedPower (f : ℕ → ℤ) (a : ℤ) (N m : ℕ) : ℤ :=
  if m ≤ N then f m else a ^ m

theorem cachedPower_sound {f : ℕ → ℤ} {a : ℤ} {N : ℕ} (h : PowerCacheValid f a N)
    (m : ℕ) : cachedPower f a N m = a ^ m := by
  unfold cachedPower
  split_ifs with hm
  · exact powerCache_sound h hm
  · rfl

namespace IntegerCoefficients

def fastAffine (choose : ℕ → ℕ → ℕ) (pa pb ps : ℕ → ℤ)
    (n : ℕ) (p : Fin (n + 1) → ℤ) : List ℤ :=
  List.ofFn (fun j : Fin (n + 1) ↦ ∑ k : Fin (n + 1),
    if (j : ℕ) ≤ (k : ℕ) then
      p k * (choose k j : ℤ) * pa ((k : ℕ) - j) * pb j * ps (n - k)
    else 0)

def fastBasis (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ) (n k : ℕ) : List ℤ :=
  List.replicate k 0 ++ List.ofFn (fun j : Fin (n - k + 1) ↦
    (choose n k : ℤ) * choose (n - k) j * sign j)

def fastExpansion (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (n : ℕ) (c : Fin (n + 1) → ℤ) : List ℤ :=
  sum (List.ofFn (fun k : Fin (n + 1) ↦ scale (c k) (fastBasis choose sign n k)))

theorem fastAffine_sound (choose : ℕ → ℕ → ℕ) (pa pb ps : ℕ → ℤ)
    (A B S : ℤ) (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hpa : ∀ m, pa m = A ^ m) (hpb : ∀ m, pb m = B ^ m)
    (hps : ∀ m, ps m = S ^ m) (n : ℕ) (p : Fin (n + 1) → ℤ) :
    fastAffine choose pa pb ps n p = affine n p A B S := by
  simp only [fastAffine, affine, hchoose, hpa, hpb, hps]

theorem fastExpansion_sound (choose : ℕ → ℕ → ℕ) (sign : ℕ → ℤ)
    (hchoose : ∀ n k, choose n k = Nat.fast_choose n k)
    (hsign : ∀ m, sign m = (-1) ^ m) (n : ℕ) (c : Fin (n + 1) → ℤ) :
    fastExpansion choose sign n c = expansion n c := by
  simp only [fastExpansion, expansion, fastBasis, basis, hchoose, hsign]

end IntegerCoefficients

end ADMM.UnitCircle.LowerCertificate
