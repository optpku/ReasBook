/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization

/-!
# Parametrized points

This module packages source parameters as points of the parametrized Lorentz
subspace and provides their ambient evaluation API.
-/

public section

noncomputable section

namespace Lorentz

/-- The source point `Ψ(a, t)`, regarded as an element of `parametrizedSubspace d`. -/
def parametrizedPoint (d : C0Seq) (a : L1Seq) (t : ℝ) : parametrizedSubspace d :=
  ⟨parametrization d (a, t),
    mem_parametrizedSubspace d _ |>.mpr ⟨a, t, parametrization_apply d a t⟩⟩

/-- The ambient value of the parametrized point is `Ψ(a, t)`. -/
@[simp]
theorem parametrizedPoint_apply (d : C0Seq) (a : L1Seq) (t : ℝ) :
    (parametrizedPoint d a t : C0Seq × L1Seq) = parametrization d (a, t) := by
  -- Coercion from the subtype reduces to its stored ambient value.
  rfl

end Lorentz
