/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ExpDioph
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.ChooseDigit
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.ForMathlib.SubmaskChoose

/-!
# Binomial coefficients and binary submasks are exponential Diophantine

Issues #33 and #34. Both reduce to packaging, now that `Nat.choose_eq_baseDigit` supplies the
coefficient extraction and `Nat.isBinarySubmask_iff_odd_choose` (#18) supplies the parity
bridge.

`chooseTerm` is **compositional over terms**, not over variable names, so it can be applied to
whatever expressions a machine encoding produces rather than only to atoms. It introduces no
new `ExpTerm` constructor: `pow`, `div` and `mod` already exist, which is precisely the reason
#16 made `div` and `mod` constructors rather than closure lemmas.

Kept in its own file so `ExpDioph` stays importable without the `Choose` hierarchy.
-/

@[expose] public section

namespace Hilbert10

variable {α : Type}

namespace ExpTerm

/-- The base used to read binomial coefficients off as digits: `2 ^ (n + 1)`. -/
def chooseBase (n : ExpTerm α) : ExpTerm α := .pow (.const 2) (.add n (.const 1))

/-- `n.choose k`, as an exponential term in `n` and `k`. -/
def chooseTerm (n k : ExpTerm α) : ExpTerm α :=
  .mod (.div (.pow (.add (chooseBase n) (.const 1)) n) (.pow (chooseBase n) k)) (chooseBase n)

@[simp] theorem eval_chooseTerm (n k : ExpTerm α) (v : α → ℕ) :
    (chooseTerm n k).eval v = (n.eval v).choose (k.eval v) := by
  simp only [chooseTerm, chooseBase, eval]
  exact (Nat.choose_eq_baseDigit (n.eval v) (k.eval v)).symm

end ExpTerm

namespace ExpDioph

/-- **#33.** The graph of `Nat.choose` is exponential Diophantine, with no witnesses. -/
theorem of_choose (n k r : ExpTerm α) :
    ExpDioph {v : α → ℕ | (n.eval v).choose (k.eval v) = r.eval v} := by
  refine (of_eq (s := ExpTerm.chooseTerm n k) (t := r)).congr fun v => ?_
  simp [Set.mem_setOf_eq]

/-- **#34.** The binary submask relation is exponential Diophantine — the consumer lemma the
route spike's `Guarded.mask` needs, in exactly the shape it was stated in. -/
theorem of_isBinarySubmask (a b : ExpTerm α) :
    ExpDioph {v : α → ℕ | Nat.IsBinarySubmask (a.eval v) (b.eval v)} := by
  refine (of_eq (s := .mod (ExpTerm.chooseTerm b a) (.const 2)) (t := .const 1)).congr fun v => ?_
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_chooseTerm]
  rw [Nat.isBinarySubmask_iff_odd_choose, Nat.odd_iff]

end ExpDioph

end Hilbert10
