/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

/- Definition 7.13.

This source item is pure canonical reuse. Lean represents the source limit
notation `α → α*` by an explicit filter parameter `l`, so the source statement
is recovered by specializing to `l = 𝓝 α*`.

The source's asymptotic equality notation is formalized by `f ~[l] g`, since
Lean reserves `≃` for equivalences. Big-O is formalized by `f =O[l] g`. The
checks below record the canonical mathlib owners together with the ratio-to-`1`
bridge `Asymptotics.isEquivalent_iff_tendsto_one`, which assumes the
denominator is eventually nonzero, the quotient-bounded big-O bridge
`Asymptotics.isBigO_iff_div_isBoundedUnder`, which assumes eventual
zero-compatibility `g x = 0 → f x = 0`, and the positive-constant
eventual-bound companion `Asymptotics.isBigO_iff'`. The source `limsup`
wording is kept as explanatory prose only, since no exact verified local
mathlib theorem with that formal statement is introduced here. -/

#check Asymptotics.IsEquivalent

#check Asymptotics.isEquivalent_iff_tendsto_one

#check Asymptotics.IsBigO

#check Asymptotics.isBigO_iff_div_isBoundedUnder

#check Asymptotics.isBigO_iff'
