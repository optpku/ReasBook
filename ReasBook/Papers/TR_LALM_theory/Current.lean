/-
Copyright (c) 2026 TR-LALM formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/
module

public import TR_LALM_theory.Assumption_2_1
public import TR_LALM_theory.Definition_2_2
public import TR_LALM_theory.Algorithm_2_1
public import TR_LALM_theory.Assumption_2_3
public import TR_LALM_theory.Proposition_2_4
public import TR_LALM_theory.Assumption_2_5
public import TR_LALM_theory.Lemma_2_6
public import TR_LALM_theory.Lemma_2_7
public import TR_LALM_theory.Lemma_2_8
public import TR_LALM_theory.Theorem_2_9
public import TR_LALM_theory.Theorem_2_10
public import TR_LALM_theory.Lemma_2_11
public import TR_LALM_theory.Theorem_2_12
public import TR_LALM_theory.Theorem_2_13
public import TR_LALM_theory.Assumption_3_1
public import TR_LALM_theory.Definition_3_2
public import TR_LALM_theory.Lemma_3_3
public import TR_LALM_theory.Lemma_3_4
public import TR_LALM_theory.Lemma_3_5
public import TR_LALM_theory.Theorem_3_6
public import TR_LALM_theory.Theorem_3_6.CanonicalRun
public import TR_LALM_theory.Theorem_3_7
public import TR_LALM_theory.Corollary_3_8
public import TR_LALM_theory.Corollary_3_8.CanonicalRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedSemantics
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergy
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPrefixInvariant
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergyRecursion
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPath
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPathRealization
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedSchedule
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedLocalization
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedExitGeometry
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalPath
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCertificate
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedOutput
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartProbability
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartAccounting
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCertifiedRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidualLaw
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidual
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCorollary
public import TR_LALM_theory.Proposition_4_1
public import TR_LALM_theory.Corollary_4_2
public import TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt
public import TR_LALM_theory.Corollary_4_2.StoppedRestart
public import TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedEnergy
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedPath
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedPathRealization
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedCanonicalPath
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedSemantics
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedSchedule
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedLocalization
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedCertificate
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedCertificateChain
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedLyapunovStep
public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedAttempt
public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedRestart
public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedCertificate
public import TR_LALM_theory.Corollary_4_2.StoppedRestartProbability
public import TR_LALM_theory.Corollary_4_2.StoppedRestartAccounting
public import TR_LALM_theory.Corollary_4_2.CertifiedStoppedRestart
public import TR_LALM_theory.Corollary_4_2.StoppedRestartResidual

/-!
# Current TR-LALM article formalization

This is the canonical import surface for the current article revision. The public
implementation module paths and declaration docstrings use the numbering of that
manuscript; helper modules are nested under the declaration they support.

The removed restoration lemma and the former Appendix C remarks are deliberately
not imported here.  The stopped-restart residual bridge is imported after the
certificate layer so the public surface includes the first-success mixture
bound as well as the finite work bounds.  The public imports of
`Corollary_3_8` and the old corrected restart modules are retained as full-tail
coupling APIs.  For the base theorem, first-exit events and prefix accounting
give the stopped semantics without treating latent tails as executed work.
The `Corollary_3_8.StoppedScheduledAttempt` and
`Corollary_4_2.Stopped*` modules additionally expose literal finite absorbing
representations for the base and optional corrected transitions, respectively.
-/

public section

end
