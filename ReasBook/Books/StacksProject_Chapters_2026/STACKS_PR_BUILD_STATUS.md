# Stacks ReasBook PR build status

This snapshot targets the stable ReasBook `v4.30.0` branch. A representative
Chap04 module is checked locally; the full chapter closure should use the
external Lake cache before it is made a merge gate.

The RC snapshot's `Mathlib.SetTheory.Cardinal.Cofinality` import is mapped
to the stable `Mathlib.SetTheory.Cardinal.Regular` module. The remaining
Chap07/Lemma_7_17_10 API-porting errors are intentionally reported here
instead of being hidden behind `sorry`.
