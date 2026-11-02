module

public import Init

@[expose] public section

universe u v

/-- A problem packages a type of admissible inputs together with, for each input, the type of
acceptable answers. -/
structure Problem where
  input : Type u
  answer : input → Type v

namespace Problem

/-- Build a problem from an admissible-input type and its acceptable-answer family. -/
def ofAnswerFamily (input : Type u) (answer : input → Type v) : Problem :=
  { input := input
    answer := answer }

/-- The type of instances of a problem, namely its admissible inputs. -/
abbrev instanceOf (P : Problem) : Type u :=
  P.input

/-- The acceptable answers assigned to a given instance of a problem. -/
abbrev answers (P : Problem) : P.instanceOf → Type v :=
  P.answer

/-- Unfolding `ofAnswerFamily` recovers the admissible-input type used to build the problem. -/
@[simp] theorem ofAnswerFamily_input
    (input : Type u)
    (answer : input → Type v) :
    (Problem.ofAnswerFamily input answer).input = input := rfl

/-- Unfolding `instanceOf` recovers the admissible-input type of a problem. -/
@[simp] theorem instanceOf_def
    (P : Problem) :
    P.instanceOf = P.input := rfl

/-- Unfolding `answers` recovers the acceptable-answer family of a problem. -/
@[simp] theorem answers_def
    (P : Problem) :
    P.answers = P.answer := rfl

end Problem

end
