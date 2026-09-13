/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator

/-!
# Rational-Time Parametrization

This module defines the continuous-linear parametrization and its range subspace.
-/

public section

noncomputable section

namespace Lorentz

/-- The continuous linear parametrization `(a, t) ↦ (-A a + t • d, a)`. -/
noncomputable def parametrization (d : C0Seq) :
    (L1Seq × ℝ) →L[ℝ] (C0Seq × L1Seq) :=
  (((-L1Seq.positiveOperator).comp (ContinuousLinearMap.fst ℝ L1Seq ℝ)) +
      (ContinuousLinearMap.snd ℝ L1Seq ℝ).smulRight d).prod
    (ContinuousLinearMap.fst ℝ L1Seq ℝ)

/-- Evaluation of the parametrization at `(a, t)`. -/
theorem parametrization_apply (d : C0Seq) (a : L1Seq) (t : ℝ) :
    parametrization d (a, t) = (-L1Seq.positiveOperator a + t • d, a) := by
  -- Reduce the continuous-linear-map constructors to their pointwise actions.
  rfl

/-- The linear subspace given by the range of the parametrization. -/
noncomputable def parametrizedSubspace (d : C0Seq) : Submodule ℝ (C0Seq × L1Seq) :=
  LinearMap.range (parametrization d).toLinearMap

/-- A pair belongs to the parametrized subspace exactly when it has the
form `(-L1Seq.positiveOperator a + t • d, a)`. -/
theorem mem_parametrizedSubspace (d : C0Seq) (z : C0Seq × L1Seq) :
    z ∈ parametrizedSubspace d ↔
      ∃ a : L1Seq, ∃ t : ℝ, z = (-L1Seq.positiveOperator a + t • d, a) := by
  constructor
  -- Extract the coordinates of a range witness and apply the evaluation rule.
  · intro hz
    rcases hz with ⟨u, rfl⟩
    refine ⟨u.1, u.2, ?_⟩
    exact (parametrization_apply d u.1 u.2).symm
  -- Conversely, the displayed parameters provide a preimage in the range.
  · rintro ⟨a, t, hz⟩
    rw [hz]
    refine ⟨(a, t), ?_⟩
    exact parametrization_apply d a t

/-- A pair `(x, u)` belongs to the parametrized subspace exactly when
`x + L1Seq.positiveOperator u` belongs to the real span of `d`. -/
theorem mk_mem_parametrizedSubspace_iff (d x : C0Seq) (u : L1Seq) :
    (x, u) ∈ parametrizedSubspace d ↔
      x + L1Seq.positiveOperator u ∈ ℝ ∙ d := by
  constructor
  -- A range witness identifies both coordinates and leaves a scalar multiple of `d`.
  · intro hz
    rcases (mem_parametrizedSubspace d (x, u)).mp hz with ⟨a, t, hz⟩
    have hu : u = a := by simpa using congrArg Prod.snd hz
    have hx : x = -L1Seq.positiveOperator u + t • d := by
      simpa [hu] using congrArg Prod.fst hz
    rw [hx]
    have hmem : t • d ∈ ℝ ∙ d := Submodule.smul_mem _ t
      (Submodule.mem_span_singleton_self d)
    simpa [hu, add_assoc] using hmem
  -- A scalar representation in the singleton span supplies the reverse range witness.
  · intro hz
    rw [Submodule.mem_span_singleton] at hz
    rcases hz with ⟨t, ht⟩
    apply (mem_parametrizedSubspace d (x, u)).mpr
    refine ⟨u, t, ?_⟩
    have hx : x + L1Seq.positiveOperator u = t • d := ht.symm
    -- Equality of the two coordinates finishes the explicit parametrization equation.
    apply Prod.ext
    · calc
        x = (x + L1Seq.positiveOperator u) - L1Seq.positiveOperator u := by abel
        _ = t • d - L1Seq.positiveOperator u := by rw [hx]
        _ = -L1Seq.positiveOperator u + t • d := by abel
    · rfl

end Lorentz
