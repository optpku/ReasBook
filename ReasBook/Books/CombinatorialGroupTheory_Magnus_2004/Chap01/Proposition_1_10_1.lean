/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open FreeMonoid

variable {n : ℕ}
variable {F : Type u} [Group F]

/-
Layer triage:
- `source-facing`: the Magnus representation attached to a chosen finite free basis.
- `core/canonical`: `FreeGroupBasis.lift` on the free-group side and `AddMonoid.End` for the
  left-regular noncommutative target action.
- `bridge/view`: the classical noncommutative formal power series algebra is realized faithfully by
  its left action on word-indexed integer series; the generator `X i` acts by prefix shift.

Domain sampling:
1. `FreeGroupBasis.lift` is the owner abstraction for defining group homomorphisms out of a free
   group with chosen basis.
2. `AddMonoid.End` is mathlib's canonical owner for a noncommutative ring of additive
   endomorphisms.
3. `FreeMonoid (Fin n)` is the canonical owner for noncommutative words on `n` generators.
4. `AddMonoid.End.applyFaithfulSMul` is the owner action showing endomorphisms are determined by
   their action on the underlying series module.

Primitive vs. derived:
the primitive target data are the word-indexed integer series on the list model of
`FreeMonoid (Fin n)` and the prefix-shift operators giving the noncommuting variables. The Magnus
homomorphism is the derived free-group map obtained from `FreeGroupBasis.lift`, so there is no
separate wrapper around the chosen basis or around generator images. -/

private abbrev foxMagnusModule (n : ℕ) := FreeMonoid (Fin n) → ℤ

/-- The left-regular Magnus target on `n` generators, realizing the noncommutative formal power
series algebra by its action on integer-valued series indexed by words in `FreeMonoid (Fin n)`. -/
abbrev foxMagnusTarget (n : ℕ) := AddMonoid.End (foxMagnusModule n)

private def foxMagnusVar (i : Fin n) : foxMagnusTarget n where
  toFun f w :=
    match w.toList with
    | [] => 0
    | j :: l => if j = i then f (ofList l) else 0
  map_zero' := by
    funext w
    cases h : w.toList with
    | nil => simp
    | cons j l =>
        by_cases hji : j = i
        · simp [hji]
        · simp [hji]
  map_add' f g := by
    funext w
    cases h : w.toList with
    | nil => simp [h]
    | cons j l =>
        by_cases hji : j = i
        · simp [h, hji, Pi.add_apply]
        · simp [h, hji, Pi.add_apply]

@[simp] private theorem foxMagnusVar_apply_one (i : Fin n) (f : foxMagnusModule n) :
    foxMagnusVar i f 1 = 0 := by
  rfl

@[simp] private theorem foxMagnusVar_apply_mul_self
    (i : Fin n) (f : foxMagnusModule n) (w : FreeMonoid (Fin n)) :
    foxMagnusVar i f (of i * w) = f w := by
  change
    (match (of i * w).toList with
      | [] => 0
      | j :: l => if j = i then f (ofList l) else 0) = f w
  simp

@[simp] private theorem foxMagnusVar_apply_mul_ne
    (i j : Fin n) (f : foxMagnusModule n) (w : FreeMonoid (Fin n)) (h : j ≠ i) :
    foxMagnusVar i f (of j * w) = 0 := by
  change
    (match (of j * w).toList with
      | [] => 0
      | k :: l => if k = i then f (ofList l) else 0) = 0
  simp [h]

private def oneAddFoxMagnusVarInvAux (i : Fin n) (f : foxMagnusModule n) :
    List (Fin n) → ℤ
  | [] => f 1
  | j :: l => f (ofList (j :: l)) - if j = i then oneAddFoxMagnusVarInvAux i f l else 0

private theorem oneAddFoxMagnusVarInvAux_zero (i : Fin n) :
    oneAddFoxMagnusVarInvAux i (0 : foxMagnusModule n) = 0 := by
  funext l
  induction l with
  | nil => simp [oneAddFoxMagnusVarInvAux]
  | cons j l ih =>
      by_cases h : j = i
      · simp [oneAddFoxMagnusVarInvAux, h, ih]
      · simp [oneAddFoxMagnusVarInvAux, h]

private theorem oneAddFoxMagnusVarInvAux_add (i : Fin n) (f g : foxMagnusModule n) :
    oneAddFoxMagnusVarInvAux i (f + g) =
      oneAddFoxMagnusVarInvAux i f + oneAddFoxMagnusVarInvAux i g := by
  funext l
  induction l with
  | nil => simp [oneAddFoxMagnusVarInvAux]
  | cons j l ih =>
      by_cases h : j = i
      · simp [oneAddFoxMagnusVarInvAux, h, ih, sub_eq_add_neg]
        abel
      · simp [oneAddFoxMagnusVarInvAux, h]

private def oneAddFoxMagnusVarInv (i : Fin n) : foxMagnusTarget n where
  toFun f w := oneAddFoxMagnusVarInvAux i f w.toList
  map_zero' := by
    funext w
    simpa using congr_fun (oneAddFoxMagnusVarInvAux_zero i) w.toList
  map_add' f g := by
    funext w
    simpa using congr_fun (oneAddFoxMagnusVarInvAux_add i f g) w.toList

@[simp] private theorem oneAddFoxMagnusVarInv_apply_ofList
    (i : Fin n) (f : foxMagnusModule n) (l : List (Fin n)) :
    oneAddFoxMagnusVarInv i f (ofList l) = oneAddFoxMagnusVarInvAux i f l := by
  rfl

private theorem one_add_foxMagnusVar_apply_inv_ofList (i : Fin n) (f : foxMagnusModule n) :
    ∀ l : List (Fin n),
      (1 + foxMagnusVar i) (oneAddFoxMagnusVarInv i f) (ofList l) = f (ofList l)
  | [] => by
      change oneAddFoxMagnusVarInvAux i f [] + foxMagnusVar i (oneAddFoxMagnusVarInv i f) 1 = f 1
      simp [oneAddFoxMagnusVarInvAux]
  | j :: l => by
      by_cases h : j = i
      · subst j
        change
          oneAddFoxMagnusVarInvAux i f (i :: l) +
              foxMagnusVar i (oneAddFoxMagnusVarInv i f) (of i * ofList l) =
            f (of i * ofList l)
        rw [foxMagnusVar_apply_mul_self]
        simp [oneAddFoxMagnusVarInvAux, sub_eq_add_neg]
      · change
          oneAddFoxMagnusVarInvAux i f (j :: l) +
              foxMagnusVar i (oneAddFoxMagnusVarInv i f) (of j * ofList l) =
            f (of j * ofList l)
        rw [foxMagnusVar_apply_mul_ne _ _ _ _ h]
        simp [oneAddFoxMagnusVarInvAux, h]

private theorem oneAddFoxMagnusVarInv_apply_one_add_ofList (i : Fin n) (f : foxMagnusModule n) :
    ∀ l : List (Fin n),
      oneAddFoxMagnusVarInv i ((1 + foxMagnusVar i) f) (ofList l) = f (ofList l)
  | [] => by
      change ((1 + foxMagnusVar i) f) 1 = f 1
      change f 1 + foxMagnusVar i f 1 = f 1
      simp
  | j :: l => by
      by_cases h : j = i
      · subst j
        change oneAddFoxMagnusVarInvAux i ((1 + foxMagnusVar i) f) (i :: l) = f (of i * ofList l)
        rw [oneAddFoxMagnusVarInvAux, if_pos rfl]
        rw [show oneAddFoxMagnusVarInvAux i ((1 + foxMagnusVar i) f) l = f (ofList l) by
          simpa using oneAddFoxMagnusVarInv_apply_one_add_ofList i f l]
        change
          f (of i * ofList l) + foxMagnusVar i f (of i * ofList l) - f (ofList l) =
            f (of i * ofList l)
        simp [sub_eq_add_neg]
      · change oneAddFoxMagnusVarInvAux i ((1 + foxMagnusVar i) f) (j :: l) = f (of j * ofList l)
        rw [oneAddFoxMagnusVarInvAux, if_neg h, ofList_cons]
        simp
        change f (of j * ofList l) + foxMagnusVar i f (of j * ofList l) = f (of j * ofList l)
        simp [h]

/-- The source-facing Magnus generator image `1 + X i` in the left-regular Magnus target. -/
def foxMagnusGeneratorUnit (i : Fin n) : Units (foxMagnusTarget n) where
  val := 1 + foxMagnusVar i
  inv := oneAddFoxMagnusVarInv i
  val_inv := by
    apply AddMonoidHom.ext
    intro f
    funext w
    change (1 + foxMagnusVar i) (oneAddFoxMagnusVarInv i f) w = f w
    rw [← ofList_toList w]
    simpa using one_add_foxMagnusVar_apply_inv_ofList i f w.toList
  inv_val := by
    apply AddMonoidHom.ext
    intro f
    funext w
    change oneAddFoxMagnusVarInv i ((1 + foxMagnusVar i) f) w = f w
    rw [← ofList_toList w]
    simpa using oneAddFoxMagnusVarInv_apply_one_add_ofList i f w.toList

/-- The Magnus homomorphism sending each basis element of a rank-`n` free group to the unit
`1 + X i`, realized here by the left-prefix action of the noncommutative variable `X i` on
word-indexed integer series. -/
def foxMagnusHom (basis : FreeGroupBasis (Fin n) F) : F →* Units (foxMagnusTarget n) :=
  basis.lift foxMagnusGeneratorUnit

/-- The Magnus homomorphism sends the chosen basis element `basis i` to the unit `1 + X i`. -/
@[simp] theorem foxMagnusHom_apply_basis (basis : FreeGroupBasis (Fin n) F) (i : Fin n) :
    foxMagnusHom basis (basis i) = foxMagnusGeneratorUnit i := by
  simp [foxMagnusHom]

-- Proof sketch: transport along `basis.repr : F ≃* FreeGroup (Fin n)` to the standard free group,
-- then apply the classical squarefree-highest-word argument for the noncommutative Magnus action on
-- formal series. The noncommutative target used above is the left-regular realization of that
-- completed Magnus algebra, so the usual argument applies unchanged.
/-- Proposition 1-10-1: if `F` is free on the basis `basis : FreeGroupBasis (Fin n) F`, then the
Magnus map sending `basis i` to `1 + X i` in the noncommutative formal power series Magnus target
is injective, hence identifies `F` with a subgroup of its unit group. -/
theorem foxMagnusHom_injective (basis : FreeGroupBasis (Fin n) F) :
    Function.Injective (foxMagnusHom basis) := sorry
