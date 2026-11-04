/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.BlockPacking
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.CleanScratch
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Internal.RunWidth

/-!
# A whole run as one number

Issue #47: packed-run completeness, semantically. An accepting run becomes a single natural
number whose blocks are the configuration codes of its successive configurations.

## Two nestings of the same construction

`fieldsCode` is used twice, at two widths, and that is the whole design.

*Inner*: a configuration of an `r`-register machine is `r + 1` fields of width `w`, so it
occupies `w * (r + 1)` bits (#45).

*Outer*: a run of `n + 1` configurations is `n + 1` blocks of width `w * (r + 1) + 1` — the
configuration, plus `BlockPacking`'s single guard bit. `Nat.IsBinarySubmask R (guardMask …)`
says exactly that every block's guard bit is clear, which by
`isBinarySubmask_guardMask_iff` is exactly that every block holds a configuration.

So extraction is `field_fieldsCode` at the outer width, and the mask obligation is the existing
`BlockPacking` characterisation. No new packing arithmetic appears here.

## Indexing

The width is written `w * (k + 1)` where `k` is the *program's* register count, so a
`Program (k + 1)` — which is what `CleanScratch` deals in — gets `w * (k + 2)` automatically.
The specialisation happens only at the `Accepts` endpoint.

## Scope

The bounded conjunction `∀ i < n, EncodedStep …` is left visible. Turning it into an exponential
Diophantine condition is #49; this file is semantics only.

## Main results

* `RegisterMachine.EncodedRun` — the packed-run predicate
* `RegisterMachine.encodedRun_packRun` — every prefix of a run packs
* `RegisterMachine.encodedRun_sound` — and every packed run is a run
* `RegisterMachine.accepts_iff_exists_encodedRun` — the two directions combined, and the exact
  statement #49 represents
-/

@[expose] public section

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- **A packed run.** `R` codes `n + 1` configurations in blocks of width `w * (k + 1) + 1`,
consecutive blocks are related by one step of `P`, and the first and last are `start` and
`finish`. -/
def EncodedRun (P : Program k) (w n R start finish : ℕ) : Prop :=
  Nat.IsBinarySubmask R (guardMask (w * (k + 1)) (n + 1)) ∧
    configField (w * (k + 1) + 1) R 0 = start ∧
      configField (w * (k + 1) + 1) R n = finish ∧
        ∀ i < n, EncodedStep P w (configField (w * (k + 1) + 1) R i)
          (configField (w * (k + 1) + 1) R (i + 1))

/-- The packing: block `i` is the code of the `i`-th configuration. -/
def packRun (P : Program k) (c : Config k) (w n : ℕ) : ℕ :=
  fieldsCode (w * (k + 1) + 1) fun i : Fin (n + 1) => configCode w (run P c i)

/-- Each block of a configuration code sits strictly inside its data field, leaving the guard
bit clear. This is the one numeric fact the outer layer needs about the inner one. -/
theorem configCode_lt_dataBound {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < dataBound (w * (k + 1)) :=
  configCode_lt_two_pow h

theorem configCode_lt_blockBase {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < 2 ^ (w * (k + 1) + 1) :=
  lt_trans (configCode_lt_two_pow h) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Extraction: the blocks of `packRun` are the configuration codes. -/
theorem field_packRun {P : Program k} {c : Config k} {w n : ℕ}
    (hfit : ∀ i ≤ n, FitsConfig w (run P c i)) {i : ℕ} (hi : i ≤ n) :
    configField (w * (k + 1) + 1) (packRun P c w n) i = configCode w (run P c i) := by
  have := field_fieldsCode
    (w := w * (k + 1) + 1) (f := fun j : Fin (n + 1) => configCode w (run P c j))
    (fun j => configCode_lt_blockBase (hfit j (by omega))) ⟨i, by omega⟩
  simpa [packRun] using this

theorem packRun_lt {P : Program k} {c : Config k} {w n : ℕ}
    (hfit : ∀ i ≤ n, FitsConfig w (run P c i)) :
    packRun P c w n < blockBase (w * (k + 1)) ^ (n + 1) :=
  fieldsCode_lt fun j => configCode_lt_blockBase (hfit j (by omega))

/-- The guard bits are clear. Immediately from `BlockPacking`'s characterisation, since each
block is a configuration code and so below `dataBound`. -/
theorem isBinarySubmask_packRun {P : Program k} {c : Config k} {w n : ℕ}
    (hfit : ∀ i ≤ n, FitsConfig w (run P c i)) :
    Nat.IsBinarySubmask (packRun P c w n) (guardMask (w * (k + 1)) (n + 1)) := by
  refine isBinarySubmask_guardMask_iff.mpr ⟨packRun_lt hfit, fun i hi => ?_⟩
  rw [show packRun P c w n / blockBase (w * (k + 1)) ^ i % blockBase (w * (k + 1))
      = configField (w * (k + 1) + 1) (packRun P c w n) i from rfl,
    field_packRun hfit (by omega)]
  exact configCode_lt_dataBound (hfit i (by omega))

/-- **Every prefix of a run packs.** The width is #46's, so no fitting hypothesis is needed. -/
theorem encodedRun_packRun {P : Program k} {c : Config k} {n : ℕ}
    (hin : ∀ i < n, (run P c i).pc < P.length) :
    EncodedRun P (runWidth P c n) n (packRun P c (runWidth P c n) n)
      (configCode (runWidth P c n) c) (configCode (runWidth P c n) (run P c n)) := by
  set w := runWidth P c n with hw
  have hfit : ∀ i ≤ n, FitsConfig w (run P c i) := fun i hi => fits_runWidth hi
  refine ⟨isBinarySubmask_packRun hfit, ?_, field_packRun hfit le_rfl, fun i hi => ?_⟩
  · rw [field_packRun hfit (Nat.zero_le n), run_zero]
  · rw [field_packRun hfit (by omega), field_packRun hfit (by omega)]
    exact encodedStep_run hi (hin i hi)

/-- **The endpoint #49 consumes.** An accepting run of `P` is a packed run from the clean input
configuration to the clean output configuration, *with the boundary constants bounded*.

The three bounds are not redundant with the mask. `EncodedRun` bounds its blocks, but an
oversized `x`, `y` or `P.length` carries inside `configCode` exactly as an oversized register
value carried inside `setField` before #45 was corrected, and the packed run would still satisfy
every block constraint. Stating them is what lets #48 recover the *exact* clean boundary
configurations rather than merely bounded ones. They are free at #46's width and cheap for
`ExpDioph`, being three `of_lt` conjuncts.

`Accepts` supplies exactly what `encodedRun_packRun` needs: the run length, the in-range program
counter at every transition, and the exit equation. Fitting comes from #46 internally and is
never an obligation on the caller. -/
theorem exists_encodedRun_of_accepts {P : Program (k + 1)} {x y : ℕ} (h : Accepts P x y) :
    ∃ n w R, x < 2 ^ w ∧ y < 2 ^ w ∧ P.length < 2 ^ w ∧
      EncodedRun P w n R
        (configCode w (⟨0, unaryConfig k x⟩ : Config (k + 1)))
        (configCode w (⟨P.length, unaryConfig k y⟩ : Config (k + 1))) := by
  obtain ⟨n, hin, hex⟩ := h
  refine ⟨n, runWidth P ⟨0, unaryConfig k x⟩ n,
    packRun P ⟨0, unaryConfig k x⟩ (runWidth P ⟨0, unaryConfig k x⟩ n) n, ?_, ?_,
    length_lt_two_pow_runWidth P ⟨0, unaryConfig k x⟩ n, ?_⟩
  · have := (fits_runWidth (P := P) (c := ⟨0, unaryConfig k x⟩) (i := 0) (n := n)
      (Nat.zero_le n)).2 0
    rw [run_zero] at this
    simpa using this
  · have := (fits_runWidth (P := P) (c := ⟨0, unaryConfig k x⟩) (i := n) (n := n) le_rfl).2 0
    rw [hex] at this
    simpa using this
  · have := encodedRun_packRun (P := P) (c := ⟨0, unaryConfig k x⟩) (n := n) hin
    rwa [hex] at this

/-- The code of a clean configuration, in closed form. The register file is zero above
register `0`, so the whole code is two terms — which is what makes the endpoint equalities of
#49 ordinary exponential terms rather than nested sums. -/
theorem configCode_unaryConfig (w p x : ℕ) :
    configCode w (⟨p, unaryConfig k x⟩ : Config (k + 1)) = p + 2 ^ w * x := by
  have h1 : (@Fin.cons (k + 1) (fun _ => ℕ) p (unaryConfig k x)) ∘ Fin.succ = unaryConfig k x := by
    funext i; simp
  have h2 : (unaryConfig k x) ∘ Fin.succ = fun _ : Fin k => 0 := by
    funext i; exact unaryConfig_of_ne (Fin.succ_ne_zero i)
  rw [configCode, fieldsCode_succ, h1, fieldsCode_succ, h2, fieldsCode_const_zero]
  simp

/-! ### Soundness

The inverse of `encodedRun_packRun`. Every carry argument was discharged in #45, so this is an
induction over block indices and nothing else. -/

/-- **A packed run really is a run.** Generic in the boundary configurations; the clean
specialisation comes after.

The invariant is that block `i`, decoded, is the `i`-th configuration of the run. It is
maintained by `decodeConfig_step_of_encodedStep`, which needs only the block bound the mask
already supplies, and `n = 0` needs no separate case because the base case is the identification
of block `0`. -/
theorem encodedRun_sound {P : Program k} {w n R : ℕ} {start finish : Config k}
    (hs : FitsConfig w start) (hf : FitsConfig w finish)
    (h : EncodedRun P w n R (configCode w start) (configCode w finish)) :
    (∀ i < n, (run P start i).pc < P.length) ∧ run P start n = finish := by
  obtain ⟨hmask, h0, hn, hstep⟩ := h
  have hblk : ∀ i < n + 1, configField (w * (k + 1) + 1) R i < 2 ^ (w * (k + 1)) := fun i hi =>
    (isBinarySubmask_guardMask_iff.mp hmask).2 i hi
  have key : ∀ i, i ≤ n → decodeConfig w (configField (w * (k + 1) + 1) R i) = run P start i := by
    intro i
    induction i with
    | zero => intro _; rw [h0, decodeConfig_configCode hs, run_zero]
    | succ i ih =>
      intro hi
      rw [decodeConfig_step_of_encodedStep (hblk i (by omega)) (hstep i (by omega)),
        ih (by omega), run_succ]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← key i (by omega)]
    exact configField_zero_lt_of_encodedStep (hstep i hi)
  · rw [← key n le_rfl, hn, decodeConfig_configCode hf]

/-- The clean boundary configurations fit as soon as their two constants do. -/
theorem fitsConfig_unaryConfig {w p x : ℕ} (hp : p < 2 ^ w) (hx : x < 2 ^ w) :
    FitsConfig w (⟨p, unaryConfig k x⟩ : Config (k + 1)) := by
  refine ⟨hp, fun i => ?_⟩
  rcases eq_or_ne i 0 with rfl | hi
  · simpa using hx
  · simp [unaryConfig_of_ne hi]

/-- **The exact endpoint.** `Accepts` — the trace relation #20 hands over — is *equivalent* to
the existence of a packed run with bounded boundary constants.

`EncodedRun` itself stays generic; the boundary bounds live only here, where they are needed to
pin the endpoints down to the clean configurations. #49 targets this right-hand side verbatim. -/
theorem accepts_iff_exists_encodedRun {P : Program (k + 1)} {x y : ℕ} :
    Accepts P x y ↔
      ∃ n w R, x < 2 ^ w ∧ y < 2 ^ w ∧ P.length < 2 ^ w ∧
        EncodedRun P w n R
          (configCode w (⟨0, unaryConfig k x⟩ : Config (k + 1)))
          (configCode w (⟨P.length, unaryConfig k y⟩ : Config (k + 1))) := by
  refine ⟨exists_encodedRun_of_accepts, ?_⟩
  rintro ⟨n, w, R, hx, hy, hlen, hrun⟩
  exact ⟨n, encodedRun_sound (fitsConfig_unaryConfig (Nat.two_pow_pos w) hx)
    (fitsConfig_unaryConfig hlen hy) hrun⟩

end RegisterMachine

end Hilbert10
