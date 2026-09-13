/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

/-!
# Surjectivity of the coordinate dual pairing

This module proves that the canonical `C0Seq`--`L1Seq` dual map is onto.
-/

public section

namespace C0Seq

/-- The strong-dual map of the coordinate pairing between real `C0Seq` and real
`L1Seq` is surjective. -/
theorem coordinateDualPairing_surjective :
    Function.Surjective coordinateDualPairing.toDual := by
  intro φ
  refine ⟨dualCoefficients φ, ?_⟩
  rw [coordinateDualPairing_toDual]
  exact l1ToDual_dualCoefficients φ

end C0Seq
