/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_9
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

-- Layer triage:
-- `source-facing`: minimal strictly quadratic cyclic words together with the Section 7 counted
-- attached-transformation sequences.
-- `core/canonical`: `CyclicWord X`, its canonical length function, the canonical cyclic-word
-- action `CyclicWord.map`, the owner specialization `specializeAtOne` from Proposition `1-7-11`,
-- and `Relation.ReflTransGen` as the owner of finite step sequences.
-- `bridge/view`: the regular one-word step is the singleton specialization of the set-level
-- attached Nielsen move from Proposition `1-7-9`, while singular steps directly use the owner
-- specialization operation from Proposition `1-7-11` together with the explicit occurrence
-- condition on the specialized generator.
-- Domain sampling:
-- 1. `AttachedElementaryNielsenTransformation` from Proposition `1-7-9` is the chapter owner
--    pattern for regular attached transformations on cyclic-word sets; the counted step relation
--    below reuses it through singleton sets.
-- 2. `CyclicWord.specializeAtOne` and `CyclicWord.IsMinimalStrictlyQuadratic` from Proposition
--    `1-7-11`
--    provide the chapter owner specialization language and the main single-word hypothesis.
-- 3. `specializeAtOne_length_eq_sub_two_or_sub_four` from Proposition `1-7-11` is the
--    chapter's exact single-word length-drop theorem reused at the singular step.
-- 4. `Relation.ReflTransGen` from mathlib is the canonical owner for finite transformation
--    sequences.
-- Primitive vs. derived:
-- the primitive Section 7 data are the regular singleton attached move and the owner
-- specialization `specializeAtOne`, assembled into the one-step relation
-- `AttachedTransformationStep`. The counted sequence relation then reuses the same primitive data
-- with the singular-step count adjoined before applying `Relation.ReflTransGen`.

/-- One attached transformation of a reduced cyclic word either applies a regular attached
elementary Nielsen transformation in the singleton-word system, or applies the singular
specialization at a generator occurring in the source word. -/
inductive AttachedTransformationStep : CyclicWord X → CyclicWord X → Prop
  | regular {q q' : CyclicWord X}
      (hstep : AttachedElementaryNielsenTransformation ({q} : Finset (CyclicWord X)) {q'}) :
      AttachedTransformationStep q q'
  | singular {q : CyclicWord X} {x : X} (hx : x ∈ q.letters) :
      AttachedTransformationStep q (CyclicWord.specializeAtOne q x)

/-- Internal predicate recording that a primitive attached-transformation step is regular. -/
private def AttachedTransformationStep.IsRegular
    {q q' : CyclicWord X} (hstep : AttachedTransformationStep q q') : Prop :=
  ∃ hregular : AttachedElementaryNielsenTransformation ({q} : Finset (CyclicWord X)) {q'},
    hstep = .regular hregular

/-- Internal singular-count transition attached to one primitive transformation step. -/
private def AttachedTransformationStep.NextSingularCount
    {q q' : CyclicWord X} (hstep : AttachedTransformationStep q q') (s t : ℕ) : Prop :=
  (hstep.IsRegular ∧ t = s) ∨ (¬ hstep.IsRegular ∧ t = s + 1)

/-- Internal counted lift of `AttachedTransformationStep`: regular steps keep the singular count,
while singular steps increment it by `1`. -/
private inductive AttachedTransformationStepCounted :
    (CyclicWord X × ℕ) → (CyclicWord X × ℕ) → Prop
  | step {q q' : CyclicWord X} {s t : ℕ} (hstep : AttachedTransformationStep q q')
      (hcount : hstep.NextSingularCount s t) :
      AttachedTransformationStepCounted (q, s) (q', t)

/-- `AttachedTransformationSequenceWithSingularCount q s q'` means that `q'` is obtained from `q`
by a finite Section 7 attached-transformation sequence with exactly `s` singular steps. -/
def AttachedTransformationSequenceWithSingularCount
    (q : CyclicWord X) (s : ℕ) (q' : CyclicWord X) : Prop :=
  Relation.ReflTransGen AttachedTransformationStepCounted (q, 0) (q', s)

/-- Proposition 1-7-12: if `q` is a minimal strictly quadratic cyclic word and `q'` is obtained
from `q` by a Section 7 attached-transformation sequence containing exactly one singular
transformation, then the cyclic length drops by `2` or by `4`. -/
-- Proof sketch: factor the unique singular step from the counted `Relation.ReflTransGen` chain.
-- The regular attached steps on the two sides preserve minimal strict quadraticity and cyclic
-- length, by the singleton-word specialization of Proposition `1-7-9` together with the
-- minimality input from Proposition `1-7-11`. The regular tail after the singular step is thus
-- controlled internally by the Section 7 owner results, so no endpoint minimality hypothesis is
-- needed in the public statement. The singular step is then the canonical specialization at one
-- generator occurring in the source word, so Proposition `1-7-11` gives a length drop of `2` or
-- `4`.
theorem length_eq_sub_two_or_sub_four_of_minimal_strictly_quadratic_and_single_singular_sequence
    {q q' : CyclicWord X}
    (hq : q.IsMinimalStrictlyQuadratic)
    (hqq' : AttachedTransformationSequenceWithSingularCount q 1 q') :
    q'.length = q.length - 2 ∨ q'.length = q.length - 4 := sorry

end
