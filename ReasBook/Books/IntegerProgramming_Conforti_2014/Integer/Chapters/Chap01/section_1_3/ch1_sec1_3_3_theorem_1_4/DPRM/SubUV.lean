module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodeAlgebra

/-!
# The difference substitution `x = u - v`

Issue #28, third piece. An integer root of `p` is a natural root of the code obtained by
replacing every variable `xᵢ` with `uᵢ - vᵢ`, because every integer is a difference of two
naturals. This file builds that code and proves what it evaluates to.

## Layout, frozen in #28

For `n := p.arity`, the transformed code uses `2 * n` variables: indices `0 .. n-1` carry `u` and
indices `n .. 2n-1` carry `v`, so variable `i` becomes `X i - X (n + i)`.

## An indexed structural recursion, not `List.enum`

`subUVMonomialFrom n i es` walks the exponent vector while carrying the index `i` of the variable
it is currently substituting for. Semantics, arity and primitive recursiveness all then follow
from the *same* recursion, which pairing the list with its indices first would obscure.

The helper contracts are strengthened with `i` for that reason: evaluation assumes
`i + es.length ≤ n`, and the arity bound is `n + i + es.length`. At `i = 0` every exponent vector
of `p` has length at most `p.arity`, which gives the frozen `2 * p.arity` bound immediately.

## Public, unlike its computability

`subUV` is one of the two reductions between the natural and integer formulations, and its
evaluation and arity theorems are meaningful on their own — so this file is API. What turns the
transformation into a many-one reduction is `Primrec subUV`, which is unsupported machinery and
stays in `Internal/SubUVComp.lean`, together with the index presentation that exists only to
prove it.

## Main definitions

* `Hilbert10.PolynomialCode.diffList`
* `Hilbert10.PolynomialCode.subUV`

## Main results

* `Hilbert10.PolynomialCode.eval_subUV`
* `Hilbert10.PolynomialCode.arity_subUV_le`
-/

@[expose] public section

namespace Hilbert10

namespace PolynomialCode

/-- The assignment `x = u - v`, componentwise. -/
def diffList (u v : List ℕ) : List ℤ :=
  List.zipWith (fun a b => (a : ℤ) - (b : ℤ)) u v

@[simp] theorem length_diffList (u v : List ℕ) :
    (diffList u v).length = min u.length v.length := by
  simp [diffList]

@[simp] theorem diffList_cons (a b : ℕ) (u v : List ℕ) :
    diffList (a :: u) (b :: v) = ((a : ℤ) - (b : ℤ)) :: diffList u v := rfl

/-- Peeling one component off the difference assignment. Proved by induction on the index
rather than through `getElem` on a `zipWith`, which simp normalises into an unhelpful shape. -/
theorem drop_diffList : ∀ (i : ℕ) (u v : List ℕ), i < u.length → i < v.length →
    (diffList u v).drop i
      = ((u.getD i 0 : ℤ) - (v.getD i 0 : ℤ)) :: (diffList u v).drop (i + 1)
  | 0, a :: u, b :: v, _, _ => by simp [List.getD]
  | i + 1, a :: u, b :: v, hu, hv => by
    have ih := drop_diffList i u v (by simpa using hu) (by simpa using hv)
    simpa [List.getD] using ih

/-- Every integer assignment is a difference of two natural ones, componentwise. -/
theorem diffList_toNat (y : List ℤ) :
    diffList (y.map Int.toNat) (y.map fun z => (-z).toNat) = y := by
  induction y with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, diffList_cons, ih]
    congr 1
    omega

/-- The variable `xᵢ` after substitution: `uᵢ - vᵢ`, at the frozen block layout. -/
def diffVar (n i : ℕ) : PolynomialCode := add (X i) (neg (X (n + i)))

/-- The substitution applied to one exponent vector, carrying the index of the variable being
substituted for. -/
def subUVMonomialFrom (n : ℕ) : ℕ → MonomialCode → PolynomialCode
  | _, [] => one
  | i, e :: es => mul (npow (diffVar n i) e) (subUVMonomialFrom n (i + 1) es)

/-- **The difference substitution.** Each term's coefficient is kept and its monomial is
substituted; the results are appended, which is what `add` does on this representation. -/
def subUV (p : PolynomialCode) : PolynomialCode :=
  ⟨p.terms.flatMap fun t => (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms⟩


/-! ### Arity -/

@[simp] theorem arity_diffVar (n i : ℕ) : (diffVar n i).arity = n + i + 1 := by
  simp only [diffVar, arity_add, arity_neg, arity_X]
  omega

theorem arity_subUVMonomialFrom (n : ℕ) : ∀ (i : ℕ) (es : MonomialCode),
    (subUVMonomialFrom n i es).arity ≤ n + i + es.length
  | _, [] => by simp [subUVMonomialFrom]
  | i, e :: es => by
    refine le_trans (arity_mul_le _ _) ?_
    have h1 : (npow (diffVar n i) e).arity ≤ n + i + 1 := by
      refine le_trans (arity_npow_le _ e) ?_
      simp
    have h2 := arity_subUVMonomialFrom n (i + 1) es
    simp only [List.length_cons, max_le_iff]
    omega

/-- **The frozen arity bound.** Every exponent vector of `p` has length at most `p.arity`, so at
`i = 0` the helper bound is `2 * p.arity`. -/
theorem arity_subUV_le (p : PolynomialCode) : (subUV p).arity ≤ 2 * p.arity := by
  refine arity_le_of_forall_term_length_le fun t ht => ?_
  simp only [subUV, List.mem_flatMap] at ht
  obtain ⟨s, hs, hts⟩ := ht
  have hlen : s.2.length ≤ p.arity := length_le_arity hs
  have hb : (mul (const s.1) (subUVMonomialFrom p.arity 0 s.2)).arity ≤ 2 * p.arity := by
    refine le_trans (arity_mul_le _ _) ?_
    have := arity_subUVMonomialFrom p.arity 0 s.2
    simp only [arity_const, max_le_iff]
    omega
  exact le_trans (length_le_arity hts) hb

/-! ### Evaluation -/

theorem eval_diffVar {n i : ℕ} {u v : List ℕ} (hu : u.length = n) (hi : i < n) :
    eval (diffVar n i) (u ++ v) = (u.getD i 0 : ℤ) - (v.getD i 0 : ℤ) := by
  have h1 : (u ++ v).getD i 0 = u.getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hu ▸ hi)]
  have h2 : (u ++ v).getD (n + i) 0 = v.getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : u.length ≤ n + i), hu]
  simp only [diffVar, eval_add, eval_neg, eval_X, h1, h2]
  ring

theorem eval_subUVMonomialFrom {n : ℕ} {u v : List ℕ} (hu : u.length = n) (hv : v.length = n) :
    ∀ (i : ℕ) (es : MonomialCode), i + es.length ≤ n →
      eval (subUVMonomialFrom n i es) (u ++ v)
        = evalMonomialInt es ((diffList u v).drop i)
  | _, [], _ => by
    rw [show subUVMonomialFrom n _ [] = one from rfl, eval_one]
    rfl
  | i, e :: es, hle => by
    have hi : i < n := by simp only [List.length_cons] at hle; omega
    have hrec := eval_subUVMonomialFrom (u := u) (v := v) hu hv (i + 1) es
      (by simp only [List.length_cons] at hle; omega)
    have hdrop := drop_diffList i u v (by omega) (by omega)
    rw [show subUVMonomialFrom n i (e :: es)
        = mul (npow (diffVar n i) e) (subUVMonomialFrom n (i + 1) es) from rfl,
      eval_mul, eval_npow, eval_diffVar hu hi, hrec, hdrop, evalMonomialInt]

/-- **The frozen correctness statement.** At the two-block layout, the substituted code evaluates
over `ℕ` to what the original evaluates to over `ℤ` at the difference assignment. -/
theorem eval_subUV (p : PolynomialCode) {u v : List ℕ}
    (hu : u.length = p.arity) (hv : v.length = p.arity) :
    eval (subUV p) (u ++ v) = evalInt p (diffList u v) := by
  simp only [subUV, eval, evalInt, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have hlen : t.2.length ≤ p.arity := length_le_arity ht
  have h := eval_subUVMonomialFrom (u := u) (v := v) hu hv 0 t.2 (by omega)
  simp only [List.drop_zero] at h
  have := eval_mul (const t.1) (subUVMonomialFrom p.arity 0 t.2) (u ++ v)
  simp only [eval_const] at this
  rw [show ((mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms.map
      fun s => s.1 * evalMonomial s.2 (u ++ v)).sum
      = eval (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)) (u ++ v) from rfl, this, h]


end PolynomialCode

end Hilbert10
