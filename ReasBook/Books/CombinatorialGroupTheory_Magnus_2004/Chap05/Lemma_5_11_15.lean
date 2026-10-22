/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

/-!
Primary domain: one-relator groups and the Nielsen-transform step that prepares a relator for an
HNN-extension argument.

Layer triage:
- `source-facing`: a one-relator presentation `⟨X ; r⟩` with at least two generators, together
  with the existence of an equivalent one-relator presentation whose relator has exponent sum zero
  in some distinguished generator.
- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
  `MulAut (FreeGroup X)` for Nielsen-transform automorphisms of the ambient free group,
  `FreeGroup.lift` for the exponent-sum homomorphism, and `Cardinal.mk X` for the lower bound on
  the size of the generator type.
- `bridge/view`: the new presentation is obtained by applying a free-group automorphism `α` to the
  relator, and `QuotientGroup.congr` together with `Subgroup.map_normalClosure` supplies the
  canonical quotient transport from `PresentedGroup (Set.singleton r)` to
  `PresentedGroup (Set.singleton (α r))`.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the project owner for a one-relator group with defining
   relator `r`.
2. `MulAut (FreeGroup X)` is the canonical owner for Nielsen moves on the ambient free group.
3. `QuotientGroup.congr` together with `Subgroup.map_normalClosure` is the canonical transport
   from a free-group automorphism to the induced equivalence of one-relator quotients.
4. `FreeGroup.lift` is the canonical way to define the exponent-sum homomorphism from the free
   group by sending one generator to `1 ∈ ℤ` and all others to `0`.
5. `Cardinal.mk X` is the project's universe-stable expression of “at least two generators”.

Primitive vs. derived:
the primitive source data are the generator type `X`, the relator `r`, and the cardinality
assumption `2 ≤ Cardinal.mk X`; the Nielsen automorphism `α`, the rewritten relator `α r`, the
distinguished generator `t` are derived existential data, while the induced presentation
equivalence is canonically supplied by `QuotientGroup.congr` and `Subgroup.map_normalClosure`, so
no wrapper structure is introduced.
-/

variable {X : Type u}

/-- The exponent sum of the generator `x` in the free-group word `r`. -/
def generatorExponentSum (x : X) (r : FreeGroup X) : ℤ :=
  let _ : DecidableEq X := Classical.decEq X
  (FreeGroup.lift (fun y ↦ Multiplicative.ofAdd (if y = x then (1 : ℤ) else 0)) r).toAdd

/-- The exponent sum of a generator in its own free-group letter is `1`. -/
@[simp] theorem generatorExponentSum_of_generator (x : X) :
    generatorExponentSum x (FreeGroup.of x) = 1 := by
  classical
  simp [generatorExponentSum]

/-- The exponent sum of `x` in a different generator letter is `0`. -/
@[simp] theorem generatorExponentSum_of_generator_ne (x y : X) (hxy : y ≠ x) :
    generatorExponentSum x (FreeGroup.of y) = 0 := by
  classical
  simp [generatorExponentSum, hxy]

-- Proof sketch: if some generator already has exponent sum `0` in `r`, keep that generator. If
-- not, choose two distinct generators and perform Nielsen moves on the free basis, replacing one
-- generator by a product with a suitable power of the other. The classical induction on the sum
-- of the absolute values of the two exponent sums decreases under this move, yielding an
-- automorphic relator whose exponent sum in one distinguished generator is `0`; the corresponding
-- one-relator quotient equivalence is the canonical `QuotientGroup.congr` transport.
/-- Auxiliary Nielsen-transform form of Lemma 5-11-15: after applying a suitable automorphism of
the ambient free group, the relator has exponent sum `0` in some distinguished generator. -/
lemma exists_automorphism_with_zero_generatorExponentSum
    (r : FreeGroup X) (hX : 2 ≤ Cardinal.mk X) :
    ∃ (α : MulAut (FreeGroup X)) (t : X), generatorExponentSum t (α r) = 0 := sorry

/-- Lemma 5-11-15: a one-relator presentation with at least two generators is equivalent to one on
the same generator type whose relator has exponent sum `0` in some distinguished generator. -/
lemma exists_equivalent_presentation_with_zero_generatorExponentSum
    (r : FreeGroup X) (hX : 2 ≤ Cardinal.mk X) :
    ∃ (r' : FreeGroup X) (_ : PresentedGroup ({r} : Set (FreeGroup X)) ≃*
      PresentedGroup ({r'} : Set (FreeGroup X))) (t : X), generatorExponentSum t r' = 0 := by
  rcases exists_automorphism_with_zero_generatorExponentSum r hX with ⟨α, t, ht⟩
  refine ⟨α r, QuotientGroup.congr
    (Subgroup.normalClosure ({r} : Set (FreeGroup X)))
    (Subgroup.normalClosure ({α r} : Set (FreeGroup X)))
    α ?_, t, ht⟩
  simpa using
    (Subgroup.map_normalClosure ({r} : Set (FreeGroup X))
      (α : FreeGroup X →* FreeGroup X) α.surjective)

end
