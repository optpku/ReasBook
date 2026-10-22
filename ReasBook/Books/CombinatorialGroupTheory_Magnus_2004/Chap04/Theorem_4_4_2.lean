/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_4_1

universe u

set_option autoImplicit false

namespace GroupPresentation

/-!
Primary domain: decision problems for finite presentations and Markov properties.

Layer triage:
- `source-facing`: a property `P` of finitely presented groups and the textbook claim that there is
  no algorithm deciding from a finite presentation whether the presented group satisfies `P`.
- `core/canonical`: `Group.IsMarkovProperty P` is the chapter owner for the hypothesis,
  `PresentedGroup` is mathlib's owner for the group defined by generators and relators, and
  `ComputablePred` is the owner predicate for algorithmic decidability on coded inputs.
- `bridge/view`: a raw finite-presentation code consists of a generator count together with a
  finite list of relator words whose letters are natural-number labels; these labels are
  interpreted as generators of `ULift (Fin n)`, with malformed labels normalized modulo `n` so the
  coding remains total for `ComputablePred`.

Domain sampling:
1. `Group.IsMarkovProperty P` from Definition `4-4-1` is the source-facing owner abstraction.
2. `GroupPresentation.HasSolvableWordProblem R` from Definition `2-1-4` is the chapter's owner
   shape for decision problems posed on finite presentations.
3. `PresentedGroup R` is the canonical owner for the group presented by relators `R`.
4. `FreeGroup.mk` is the canonical evaluation map from finite signed words to free-group elements,
   while `ComputablePred` is mathlib's owner for solvability of a decision problem on coded input.

Primitive vs. derived:
- primitive public data: only the property `P`;
- derived bridge data: the raw code `(n, rels)`, its normalization to relator words on
  `ULift (Fin n)`, and the resulting relator set.
-/

private abbrev PresentationCode := ℕ × List (List (ℕ × Bool))

private def codedLetter : (n : ℕ) → ℕ × Bool → Option (ULift (Fin n) × Bool)
  | 0, _ => none
  | m + 1, (i, ε) => some (⟨⟨i % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩⟩, ε)

private def codedWord (n : ℕ) : List (ℕ × Bool) → List (ULift (Fin n) × Bool) :=
  List.filterMap (codedLetter n)

private def relatorSetOfCode (c : PresentationCode) : Set (FreeGroup (ULift.{u} (Fin c.1))) :=
  match c with
  | (n, rels) => FreeGroup.mk '' (codedWord n '' {w | w ∈ rels})

private abbrev presentedGroupOfCode (c : PresentationCode) : Type u :=
  PresentedGroup (relatorSetOfCode c)

/-- A property of finitely presented groups has solvable recognition problem when one can compute
from a finite presentation whether the presented group has that property. -/
def HasSolvableRecognitionProblem (P : (G : Type u) → [Group G] → Prop) : Prop :=
  ComputablePred fun c : PresentationCode ↦
    P (presentedGroupOfCode c)

variable (P : (G : Type u) → [Group G] → Prop)

-- Proof sketch: Adian-Rabin encodes the obstruction group from `IsMarkovProperty P` into a finite
-- presentation so that deciding whether the presented group has `P` would decide whether a given
-- word becomes trivial in an arbitrary finitely presented group. Since the latter is unsolvable,
-- the recognition problem for `P` cannot be computable.
/-- Theorem 4-4-2: every Markov property of finitely presented groups has unsolvable recognition
problem. -/
theorem not_hasSolvableRecognitionProblem [Group.IsMarkovProperty P] :
    ¬ HasSolvableRecognitionProblem P := sorry

end GroupPresentation
