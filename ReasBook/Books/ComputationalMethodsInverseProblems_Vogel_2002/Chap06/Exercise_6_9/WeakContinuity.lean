/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_22.WeakSeqTendsto

public section

universe u v

variable {Q : Type u} {Y : Type v}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The map on weak topologies induced by `F : Q → Y`. -/
noncomputable def toWeakMap (F : Q → Y) : WeakSpace ℝ Q → WeakSpace ℝ Y :=
  fun q ↦ toWeakSpace ℝ Y (F ((toWeakSpace ℝ Q).symm q))

/-- Evaluating `toWeakMap F` on the canonical weak-space point recovers `F`. -/
@[simp] theorem toWeakMap_apply (F : Q → Y) (q : Q) :
    toWeakMap F (toWeakSpace ℝ Q q) = toWeakSpace ℝ Y (F q) :=
  by simp [toWeakMap]

/-- Continuity of the transported weak-topology map sends weakly convergent sequences to weakly
convergent sequences. -/
theorem Continuous.weakSeqTendsto_toWeakMap {F : Q → Y} (hF : Continuous (toWeakMap F))
    {f : ℕ → Q} {q : Q} (hf : weakSeqTendsto f q) :
    weakSeqTendsto (fun n ↦ F (f n)) (F q) := by
  rw [weakSeqTendsto_iff] at hf ⊢
  convert (hF.tendsto (toWeakSpace ℝ Q q)).comp hf using 1
  · ext n
    simp
  · simp
