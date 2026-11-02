module

/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CodeRfind

/-!
# Every code has a machine

Issue #44. The constructor library is complete, so this is a structural induction that selects
the right closure theorem in each case.

## Proposition-valued on purpose

`exists_cleanMachine` is an existential, not a `Code → Program` compiler with a correctness
certificate. Nothing downstream needs the machine as *data*: #21 arithmetises a fixed machine's
trace relation, and fixing it is existential elimination in a `Prop`. Producing a dependent
compiler object would be the verified-DSL project (#29) arriving through the side door — the same
argument that made DPRM a semantic theorem in the first place.

## The graph relation

`Accepts` (in `CleanScratch`) is trace-level: it says the machine takes the clean configuration
for `x` to the clean configuration for `y`, with no mention of the function computed.
`accepts_iff` is the only place the two meet, and `exists_machine_graph` is what #21 consumes.
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- **Every code is computed by a clean machine.** -/
theorem exists_cleanMachine (c : Code) :
    ∃ (k : ℕ) (P : Program (k + 1)), CleanPartComputesUnary P c.eval := by
  induction c with
  | zero =>
    exact ⟨0, zeroMachine 0, computesUnary_zeroMachine.toPart.toClean.congr fun x => rfl⟩
  | succ =>
    exact ⟨0, succMachine 0, computesUnary_succMachine.toPart.toClean.congr fun x => rfl⟩
  | left => exact ⟨5, leftMachine, cleanPartComputesUnary_leftMachine.congr fun x => rfl⟩
  | right => exact ⟨5, rightMachine, cleanPartComputesUnary_rightMachine.congr fun x => rfl⟩
  | pair cf cg ihf ihg =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    obtain ⟨kg, Pg, hg⟩ := ihg
    exact ⟨kf + kg + 12, _, hf.codePair hg⟩
  | comp cf cg ihf ihg =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    obtain ⟨kg, Pg, hg⟩ := ihg
    have hf' := hf.widen (k' := max kf kg)
      (σ := Fin.castLE (by omega)) (Fin.castLE_injective _) (by simp)
    have hg' := hg.widen (k' := max kf kg)
      (σ := Fin.castLE (by omega)) (Fin.castLE_injective _) (by simp)
    exact ⟨max kf kg, _, (hg'.comp hf').congr fun x => rfl⟩
  | prec cf cg ihf ihg =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    obtain ⟨kg, Pg, hg⟩ := ihg
    exact ⟨kf + kg + 31, _, CleanPartComputesUnary.codePrec (k := kf) (k' := kg) Pf Pg hf hg⟩
  | rfind' cf ihf =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    exact ⟨kf + 19, _, CleanPartComputesUnary.codeRfind hf⟩

/-- **The graph endpoint.** A fixed machine whose trace relation is exactly the code's graph —
which is what #21 arithmetises. -/
theorem exists_machine_graph (c : Code) :
    ∃ (k : ℕ) (P : Program (k + 1)), ∀ x y, Accepts P x y ↔ y ∈ c.eval x := by
  obtain ⟨k, P, h⟩ := exists_cleanMachine c
  exact ⟨k, P, fun x y => h.accepts_iff x y⟩

end RegisterMachine

end Hilbert10
