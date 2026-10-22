/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_10_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Monoid.Coprod

set_option autoImplicit false

noncomputable section

namespace SmallCancellationProduct

section

variable {H : Type u} [Group H]

open Monoid.CoprodI
open MulEquiv

/-!
Primary domain: the explicit Section `10` small-cancellation product built from a countable group
and the cyclic groups of orders `5` and `7`.

Layer triage:
- `source-facing`: the chosen enumeration `enumerate : ℕ → H`, the explicit relators `r₀, r₁, …`
  in `H * C₅ * C₇`, and the resulting quotient group.
- `core/canonical`: `Monoid.CoprodI` is the owner for the three-factor free product,
  `Monoid.CoprodI.condition_c_prime` is the owner predicate for the `C'(1 / 10)` hypothesis,
  `IsHopfian`, `IsCohopfian`, `Subgroup.center`, and `JA(_)` are the owner predicates for the
  resulting abstract group properties.
- `bridge/view`: `Monoid.Coprod.lift` gives the canonical map from `C₅ * C₇` into the quotient,
  and the three factor embeddings are the obvious compositions with the quotient map.

Domain sampling:
1. `Monoid.CoprodI` from mathlib is the canonical owner for the free product of an indexed family
   of groups, and Section `10` already phrases small-cancellation over free products with that
   owner in [Theorem_5_10_1](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap05/Theorem_5_10_1.lean).
2. `Monoid.CoprodI.condition_c_prime` and its notation `C'(\lambda)[R]` are the chapter owner
   APIs for the symmetrized small-cancellation hypothesis.
3. `IsHopfian` from [Proposition_1_3_5](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap01/Proposition_1_3_5.lean)
   is the owner predicate for the Hopfian conclusion, and the same file now houses the matching
   cohopfian owner.
4. `MulAut.innerAutomorphismSubgroup` from
   [Proposition_1_4_5](/volume/math/AI4M/users/zcwang/bookrepo/CombinatorialGroupTheory/CombinatorialGroupTheory/Items/Chap01/Proposition_1_4_5.lean)
   is the canonical owner for “every automorphism is inner”, and the textbook notation `JA(G)` is
   the source-facing theorem surface for that owner, so completeness is expressed by the pair
   `Subgroup.center G = ⊥` and `JA(G) = ⊤`.

Primitive vs. derived:
- primitive source data: the group `H` and the chosen sequence `enumerate : ℕ → H`;
- canonical derived data: the three-factor free product, the explicit relators, the relator set,
  the quotient map, and the induced factor maps;
- derived API: the `C'(1 / 10)` statement, the quotient-of-`C₅ * C₇` surjection, the three factor
  embeddings, and the Hopfian/complete/cohopfian conclusions.
-/

/-- The cyclic group of order `5`, written multiplicatively. -/
abbrev C5 := Multiplicative (ZMod 5)

/-- The cyclic group of order `7`, written multiplicatively. -/
abbrev C7 := Multiplicative (ZMod 7)

/-- The three factors `H`, `C₅`, and `C₇` of the ambient free product. -/
abbrev Factors (H : Type u) : Fin 3 → Type u
  | 0 => H
  | 1 => ULift.{u} C5
  | _ => ULift.{u} C7

instance factorsGroup : ∀ i, Group (Factors H i)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

local notation "F" => Monoid.CoprodI (Factors H)

private abbrev factorHom : ∀ i : Fin 3, Factors H i →* F
  | 0 => Monoid.CoprodI.of
  | 1 => Monoid.CoprodI.of
  | 2 => Monoid.CoprodI.of

/-- The distinguished generator of the `C₅` factor. -/
def xGenerator : C5 :=
  Multiplicative.ofAdd (1 : ZMod 5)

/-- The distinguished generator of the `C₇` factor. -/
def yGenerator : C7 :=
  Multiplicative.ofAdd (1 : ZMod 7)

/-- The image of the distinguished generator of `C₅` in the ambient free product. -/
def x : F :=
  factorHom 1 (ulift.symm xGenerator)

/-- The image of the distinguished generator of `C₇` in the ambient free product. -/
def y : F :=
  factorHom 2 (ulift.symm yGenerator)

/-- The image of the `n`th listed element of `H` in the ambient free product. -/
def h (enumerate : ℕ → H) (n : ℕ) : F :=
  factorHom 0 (enumerate n)

/-- The basic block `((x y)^j x y^2)` occurring in the Section `10` relators. -/
def block (j : ℕ) : F :=
  (x * y) ^ j * x * y ^ 2

/-- The ordered product of consecutive blocks, used in the explicit relators. -/
def blockProduct (start len : ℕ) : F :=
  ((List.range' start len).map block).prod

/-- The initial relator
`r₀ = x y x y^2 (x y)^2 x y^2 ... (x y)^80 x y^2`. -/
def relatorZero : F :=
  blockProduct 1 80

/-- The subsequent relators
`r_{n+1} = h_n⁻¹ ∏_{j = 80 (n + 1) + 1}^{80 (n + 3)} ((x y)^j x y^2)`. -/
def relator (enumerate : ℕ → H) : ℕ → F
  | 0 => relatorZero
  | n + 1 => (h enumerate n)⁻¹ * blockProduct (80 * (n + 1) + 1) 160

/-- The raw relator set generated by the explicit Section `10` relators. -/
def relatorSet (enumerate : ℕ → H) : Set F :=
  Set.range (relator enumerate)

/-- The quotient of the ambient free product by the normal closure of the explicit relator set. -/
abbrev quotient (enumerate : ℕ → H) :=
  F ⧸ Subgroup.normalClosure (relatorSet enumerate)

/-- The quotient map from the ambient free product to the explicit Section `10` quotient. -/
abbrev quotientMap (enumerate : ℕ → H) : F →* quotient enumerate :=
  QuotientGroup.mk' (Subgroup.normalClosure (relatorSet enumerate))

/-- The induced map from the `H` factor into the explicit quotient. -/
abbrev embedH (enumerate : ℕ → H) : H →* quotient enumerate :=
  (quotientMap enumerate).comp (factorHom 0)

/-- The induced map from the `C₅` factor into the explicit quotient. -/
abbrev embedC5 (enumerate : ℕ → H) : C5 →* quotient enumerate :=
  ((quotientMap enumerate).comp (factorHom 1)).comp ulift.symm.toMonoidHom

/-- The induced map from the `C₇` factor into the explicit quotient. -/
abbrev embedC7 (enumerate : ℕ → H) : C7 →* quotient enumerate :=
  ((quotientMap enumerate).comp (factorHom 2)).comp ulift.symm.toMonoidHom

/-- The canonical map from `C₅ * C₇` to the explicit quotient. -/
abbrev cyclicFactorsHom (enumerate : ℕ → H) : C5 ∗ C7 →* quotient enumerate :=
  Monoid.Coprod.lift (embedC5 enumerate) (embedC7 enumerate)

section

variable (enumerate : ℕ → H)

-- Proof sketch: this is the standard overlap computation from the textbook. The block structure
-- forces every common piece to be shorter than one tenth of a relator.
/-- The explicit relator set of Theorem 5-10-5 satisfies the free-product small-cancellation
condition `C'(1 / 10)`. -/
theorem condition_c_prime_one_tenth :
    C'((1 / 10 : ℝ))[relatorSet enumerate] := by
  sorry

private theorem condition_c_prime_one_sixth :
    C'((1 / 6 : ℝ))[relatorSet enumerate] := by
  intro q hq piece hpart hpiece
  have hpiece_lt := condition_c_prime_one_tenth enumerate hq hpart hpiece
  nlinarith

-- Proof sketch: the relators are built from strictly increasing block exponents, so the standard
-- “piece versus power” argument shows that none of them is a proper power.
/-- No relator in the explicit set of Theorem 5-10-5 is a proper power. -/
theorem not_isProperPower_of_mem_relatorSet {r : F} (hr : r ∈ relatorSet enumerate) :
    ¬ IsProperPower r := by
  sorry

-- Proof sketch: surjectivity of `enumerate` lets one eliminate each `h_n` from the quotient by
-- the relator `r_{n+1}`, so the quotient is generated by the images of `x` and `y`.
/-- The explicit quotient from Theorem 5-10-5 is a quotient of `C₅ * C₇`. -/
theorem surjective_cyclicFactorsHom (henum : Function.Surjective enumerate) :
    Function.Surjective (cyclicFactorsHom enumerate) := by
  sorry

-- Proof sketch: every surjective endomorphism is controlled by its values on the images of `x`
-- and `y`; the torsion theorem and the relator geometry force those images to be conjugate back
-- to the original generators.
/-- The explicit quotient of Theorem 5-10-5 is Hopfian. -/
theorem isHopfian_quotient (henum : Function.Surjective enumerate) :
    IsHopfian (quotient enumerate) := by
  sorry

-- Proof sketch: the same analysis of the images of `x` and `y` shows that every automorphism is
-- inner, while a central element must already be a power of the `C₅` generator and is therefore
-- trivial.
/-- The explicit quotient of Theorem 5-10-5 is complete: its center is trivial and every
automorphism is inner. -/
theorem complete_quotient (henum : Function.Surjective enumerate) :
    Subgroup.center (quotient enumerate) = ⊥ ∧
      JA(quotient enumerate) = ⊤ := by
  sorry

-- Proof sketch: if `H` has no element of order `5`, an injective endomorphism must send the
-- `C₅` generator back into the distinguished `C₅` factor, and the same relator comparison as in
-- the Hopfian case forces the endomorphism to be an automorphism.
/-- If `H` has no element of order `5`, then the explicit quotient of Theorem 5-10-5 is
cohopfian. -/
theorem isCohopfian_quotient_of_no_order_five
    (hno5 : ∀ h' : H, orderOf h' ≠ 5) (henum : Function.Surjective enumerate) :
    IsCohopfian (quotient enumerate) := by
  sorry

-- Proof sketch: combine the preceding theorems for the explicit quotient owner.
/-- Theorem 5-10-5: for the explicit quotient built from the relators `r₀, r₁, ...` attached to
the chosen enumeration of `H`, the relator set satisfies `C'(1 / 10)`, the quotient is a quotient
of `C₅ * C₇`, the factors `H`, `C₅`, and `C₇` embed, the quotient is Hopfian and complete, and it
is cohopfian whenever `H` has no element of order `5`. -/
theorem quotient_properties (henum : Function.Surjective enumerate) :
    C'((1 / 10 : ℝ))[relatorSet enumerate] ∧
      Function.Surjective (cyclicFactorsHom enumerate) ∧
      Function.Injective (embedH enumerate) ∧
      Function.Injective (embedC5 enumerate) ∧
      Function.Injective (embedC7 enumerate) ∧
      IsHopfian (quotient enumerate) ∧
      (Subgroup.center (quotient enumerate) = ⊥ ∧
        JA(quotient enumerate) = ⊤) ∧
      ((∀ h' : H, orderOf h' ≠ 5) → IsCohopfian (quotient enumerate)) := by
  refine ⟨condition_c_prime_one_tenth enumerate, surjective_cyclicFactorsHom enumerate henum,
    ?_, ?_, ?_, isHopfian_quotient enumerate henum,
    complete_quotient enumerate henum, ?_⟩
  · simpa [embedH, quotientMap] using
      Monoid.CoprodI.factor_injective_in_quotient_of_condition_c_prime
        (condition_c_prime_one_sixth enumerate) 0
  · simpa [embedC5, quotientMap] using
      (Monoid.CoprodI.factor_injective_in_quotient_of_condition_c_prime
        (condition_c_prime_one_sixth enumerate) 1).comp
        ((ulift.symm : C5 ≃* ULift C5).injective : Function.Injective (ulift.symm : C5 → ULift C5))
  · simpa [embedC7, quotientMap] using
      (Monoid.CoprodI.factor_injective_in_quotient_of_condition_c_prime
        (condition_c_prime_one_sixth enumerate) 2).comp
        ((ulift.symm : C7 ≃* ULift C7).injective : Function.Injective (ulift.symm : C7 → ULift C7))
  intro hno5
  exact isCohopfian_quotient_of_no_order_five enumerate hno5 henum

end

section

variable (enumerate : ℕ → H)
variable [Group.IsFinitelyPresented H]

-- Proof sketch: once every `h_n` is eliminated by the relators, the quotient admits a finite
-- two-generator presentation whenever the original group `H` is finitely presented.
/-- If `H` is finitely presented, then the explicit quotient of Theorem 5-10-5 is finitely
presented as well. -/
theorem isFinitelyPresented_quotient (henum : Function.Surjective enumerate) :
    Group.IsFinitelyPresented (quotient enumerate) := by
  sorry

end

end

end SmallCancellationProduct
