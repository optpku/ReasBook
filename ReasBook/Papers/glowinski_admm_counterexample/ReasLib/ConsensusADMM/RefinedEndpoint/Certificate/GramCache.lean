/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Tactic.IntervalCases

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF0
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF1
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF2
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF3
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF4
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF5
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF6
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF7
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF8
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF9
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF10
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF11
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF12
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF13
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF14
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FF15
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT0
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT1
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT2
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT3
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT4
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT5
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT6
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT7
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT8
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT9
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT10
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT11
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT12
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT13
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT14
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.FT15
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF0
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF1
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF2
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF3
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF4
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF5
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF6
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF7
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF8
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF9
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF10
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF11
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF12
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF13
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF14
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TF15
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT0
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT1
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT2
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT3
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT4
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT5
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT6
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT7
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT8
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT9
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT10
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT11
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT12
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT13
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT14
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.GramCacheChecks.TT15

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

/-- The proposed cache equals the faithful integer Gram evaluator at every entry. -/
theorem cachedGramNumerator_correct (a b : Bool) (d : Fin 1024) :
    cachedGramNumerator a b d = gramNumerator a b d := by
  cases a with
  | false =>
    cases b with
    | false =>
      have hdiv : d.val / 64 < 16 := by omega
      interval_cases hq : d.val / 64
      · have h := gramCacheFF0 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 0 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF1 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 64 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF2 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 128 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF3 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 192 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF4 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 256 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF5 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 320 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF6 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 384 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF7 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 448 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF8 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 512 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF9 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 576 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF10 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 640 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF11 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 704 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF12 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 768 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF13 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 832 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF14 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 896 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFF15 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 960 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
    | true =>
      have hdiv : d.val / 64 < 16 := by omega
      interval_cases hq : d.val / 64
      · have h := gramCacheFT0 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 0 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT1 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 64 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT2 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 128 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT3 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 192 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT4 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 256 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT5 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 320 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT6 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 384 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT7 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 448 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT8 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 512 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT9 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 576 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT10 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 640 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT11 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 704 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT12 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 768 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT13 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 832 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT14 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 896 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheFT15 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 960 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
  | true =>
    cases b with
    | false =>
      have hdiv : d.val / 64 < 16 := by omega
      interval_cases hq : d.val / 64
      · have h := gramCacheTF0 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 0 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF1 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 64 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF2 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 128 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF3 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 192 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF4 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 256 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF5 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 320 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF6 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 384 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF7 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 448 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF8 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 512 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF9 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 576 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF10 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 640 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF11 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 704 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF12 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 768 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF13 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 832 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF14 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 896 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTF15 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 960 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
    | true =>
      have hdiv : d.val / 64 < 16 := by omega
      interval_cases hq : d.val / 64
      · have h := gramCacheTT0 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 0 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT1 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 64 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT2 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 128 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT3 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 192 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT4 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 256 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT5 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 320 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT6 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 384 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT7 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 448 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT8 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 512 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT9 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 576 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT10 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 640 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT11 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 704 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT12 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 768 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT13 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 832 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT14 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 896 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h
      · have h := gramCacheTT15 ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
        have he : 960 + d.val % 64 = d.val := by omega
        simpa only [Fin.val_mk, he] using h

theorem cachedGramEntryNumerator_correct (i j : ℕ) :
    cachedGramEntryNumerator i j = gramEntryNumerator i j := by
  exact cachedGramNumerator_correct _ _ ⟨_, Nat.mod_lt _ (by decide)⟩

theorem cachedPairNumerator_correct (A B : SparseVector) :
    cachedPairNumerator A B = pairNumerator A B := by
  simp only [cachedPairNumerator, pairNumerator, cachedGramEntryNumerator_correct]

end ConsensusADMM.RefinedEndpoint.Certificate
