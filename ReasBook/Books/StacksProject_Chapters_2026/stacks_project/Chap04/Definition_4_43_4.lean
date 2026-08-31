module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Lemma_4_43_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X : C)

/- Domain sampling:
- Primary domain: monoidal category theory, specifically invertible objects detected by tensoring
  endofunctors.
- Core/canonical declarations inspected:
  - `tensorLeft`
  - `tensorRight`
  - `Functor.IsEquivalence`
  - `tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`
  - `tensorLeft_isEquivalence_iff_exists_tensor_inverse`
- Owner abstraction: the canonical predicate is `(tensorLeft X).IsEquivalence`.
- Layer triage:
  - `source-facing`: the textbook invertibility predicate for the fixed object `X`;
  - `core/canonical`: `Functor.IsEquivalence`, specialized to `tensorLeft X`;
  - `bridge/view`: the imported companion theorems
    `tensorLeft_isEquivalence_iff_tensorRight_isEquivalence` and
    `tensorLeft_isEquivalence_iff_exists_tensor_inverse` from Lemma `4.43.3`.
- Primitive vs. derived:
  - primitive data: none beyond the owner predicate itself;
  - derived API: the imported bridge theorems relating that predicate to right tensoring and to
    two-sided tensor inverse data, with no additional local wrapper API needed here.
-/

/- Definition 4.43.4: the canonical predicate expressing that an object `X` of a monoidal
category is invertible is that tensoring on the left by `X` is an equivalence. By Lemma 4.43.3,
this is equivalent to tensoring on the right by `X` being an equivalence and to the existence of
a two-sided tensor inverse for `X`. -/
#check (tensorLeft X).IsEquivalence

/- Companion recall: the left-tensor criterion is equivalent to the right-tensor criterion. -/
recall tensorLeft_isEquivalence_iff_tensorRight_isEquivalence

/- Companion recall: the left-tensor criterion is equivalent to the existence of a two-sided
tensor inverse. -/
recall tensorLeft_isEquivalence_iff_exists_tensor_inverse

end CategoryTheory
