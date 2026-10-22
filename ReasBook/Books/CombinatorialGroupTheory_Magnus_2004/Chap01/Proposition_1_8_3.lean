/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Monoid.Coprod
open Monoid.Coprod

section

variable {F : Type u} [Group F]

-- Layer triage:
-- `source-facing`: a one-variable equation `equation : F ∗ Multiplicative ℤ` over the free group
-- `F`, together with Section `8` parametric words and their value sets in `F`.
-- `core/canonical`: `F ∗ Multiplicative ℤ` is the chapter/mathlib owner object for one-variable
-- equations, `SplitToInfiniteCyclic` is the upstream chapter owner for a split retraction onto
-- `Multiplicative ℤ`, `lift (MonoidHom.id F) (zpowersHom F x)` is the canonical evaluation map at
-- `x : F`, `Set.range` is the canonical owner construction for the value set of a fixed
-- parametric word, and `IsFreeGroup F` is the source-faithful freeness hypothesis.
-- `bridge/view`: a parametric word carries a fixed `SplitToInfiniteCyclic` datum, and the
-- associated one-variable equation is the derived bridge `ParametricWord.toEquation`.
-- Domain sampling:
-- 1. Proposition `1-8-1` introduces the owner abstraction `SplitToInfiniteCyclic` and the
--    canonical bridge `inducedSplitRetraction`.
-- 2. Proposition `2-5-3` evaluates one-variable words directly by `lift φ (zpowersHom G g)`,
--    again using `F ∗ Multiplicative ℤ` as the owner object.
-- 3. `Set.range` is the canonical owner of the set of values attained by a fixed parametric word.
-- Primitive vs. derived:
-- the primitive public data of Proposition `1-8-3` are the equation `equation : F ∗
-- Multiplicative ℤ` and a parametric word with its fixed parameter group, split retraction, and
-- ambient coproduct word. Its associated one-variable equation, evaluation map, and value set are
-- derived canonically from that owner object.

/-- The solution set of a one-variable equation `equation : F ∗ Multiplicative ℤ`, evaluated in
the free group `F` by sending the distinguished infinite-cyclic factor to `x : F`. -/
def equationSolutionSet (equation : F ∗ Multiplicative ℤ) : Set F :=
  { x | lift (MonoidHom.id F) (zpowersHom F x) equation = 1 }

@[simp] theorem mem_equationSolutionSet_iff (equation : F ∗ Multiplicative ℤ) (x : F) :
    x ∈ equationSolutionSet equation ↔
      lift (MonoidHom.id F) (zpowersHom F x) equation = 1 := by
  rfl

end

section

variable {F : Type u} [Group F]

/-- A Section `8` parametric word over `F` consists of a parameter group with a fixed split
retraction onto the infinite cyclic group, together with a coproduct word in `F ∗ R`. -/
structure ParametricWord (F : Type u) [Group F] where
  parameterGroup : Type v
  instGroupParameterGroup : Group parameterGroup
  specialization : @SplitToInfiniteCyclic parameterGroup instGroupParameterGroup
  word : F ∗ parameterGroup

attribute [instance] ParametricWord.instGroupParameterGroup

namespace ParametricWord

/-- The canonical bridge from a parametric word to its associated one-variable equation. -/
def toEquation (paramWord : ParametricWord F) : F ∗ Multiplicative ℤ :=
  inducedSplitRetraction paramWord.specialization paramWord.word

/-- Evaluate a parametric word at `x : F` by evaluating its associated one-variable equation in
`F`. -/
def eval (paramWord : ParametricWord F) (x : F) : F :=
  lift (MonoidHom.id F) (zpowersHom F x) paramWord.toEquation

/-- The value set of a parametric word consists of all values it attains under evaluation in `F`.
-/
def valueSet (paramWord : ParametricWord F) : Set F :=
  Set.range paramWord.eval

@[simp] theorem mem_valueSet_iff (paramWord : ParametricWord F) (g : F) :
    g ∈ paramWord.valueSet ↔ ∃ x : F, paramWord.eval x = g := by
  rfl

end ParametricWord

/-- Proposition 1-8-3: for a one-variable equation `equation : F ∗ Multiplicative ℤ` over a free
group `F`, there exists a finite set of Section `8` parametric words whose value sets cover
exactly the solution set of `equation`. -/
-- Proof sketch: Section `8` analyzes a one-variable equation over a free group by passing to a
-- finite family of parametric words. Each such word carries its own fixed parameter group and
-- split retraction onto the infinite cyclic group, hence a canonical associated equation and value
-- set. The union of those value sets is exactly the solution set of the original equation.
theorem exists_finite_parametric_word_set [IsFreeGroup F] (equation : F ∗ Multiplicative ℤ) :
    ∃ W : Set (ParametricWord F),
      W.Finite ∧
        (⋃ paramWord ∈ W, paramWord.valueSet) = equationSolutionSet equation := sorry

end
