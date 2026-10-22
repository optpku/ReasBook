/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory MeasurableEquiv Preorder ProbabilityTheory

universe u

namespace ProbabilityTheory.Kernel

section

variable {X : ℕ → Type u}
variable [∀ n, MeasurableSpace (X n)]
variable (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
variable (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]

-- Proof sketch: use mathlib's canonical Ionescu-Tulcea trajectory measure
-- `Kernel.trajMeasure μ₀ κ` for existence. For uniqueness, compare any competing probability
-- measure with the same finite-dimensional marginals on every restriction map `frestrictLe n`,
-- then apply projective-limit uniqueness for the induced family of finite-dimensional laws.
/-- Theorem 14.32: an initial probability law `μ₀` and Markov kernels `κ n` determine a unique
probability measure on the infinite trajectory space whose finite-dimensional marginals are the
iterated laws from `(14.11)`. -/
theorem existsUnique_probability_measure_with_prescribed_finite_dimensional_marginals
    :
    ∃! μ : Measure (Π n, X n),
      IsProbabilityMeasure μ ∧
        ∀ n : ℕ,
          μ.map (frestrictLe n) =
            partialTraj κ 0 n ∘ₘ μ₀.map (piUnique (fun i : Iic 0 ↦ X i)).symm := by
  let μinit : Measure (Π i : Iic 0, X i) := μ₀.map (piUnique (fun i : Iic 0 ↦ X i)).symm
  let μfin : (n : ℕ) → Measure (Π i : Iic n, X i) := fun n ↦ partialTraj κ 0 n ∘ₘ μinit
  let P : (I : Finset ℕ) → Measure (Π i : I, X i) := inducedFamily μfin
  have hμfin : ∀ a b : ℕ, ∀ hab : a ≤ b, (μfin b).map (frestrictLe₂ hab) = μfin a := by
    intro a b hab
    rw [show μfin b = partialTraj κ 0 b ∘ₘ μinit by rfl]
    rw [show μfin a = partialTraj κ 0 a ∘ₘ μinit by rfl]
    rw [Measure.map_comp _ _ (measurable_frestrictLe₂ hab), partialTraj_map_frestrictLe₂ 0 hab]
  have hP : IsProjectiveMeasureFamily P := by
    dsimp [P]
    exact isProjectiveMeasureFamily_inducedFamily μfin hμfin
  have hPIic (n : ℕ) : P (Iic n) = μfin n := by
    dsimp [P]
    rw [inducedFamily_Iic]
  have hlimit {ν : Measure (Π n, X n)} (hν : ∀ n, ν.map (frestrictLe n) = μfin n) :
      IsProjectiveLimit ν P := by
    refine (isProjectiveLimit_nat_iff hP ν).2 fun n ↦ ?_
    rw [hPIic n]
    exact hν n
  refine ⟨trajMeasure μ₀ κ, ?_, ?_⟩
  · refine ⟨inferInstance, ?_⟩
    exact trajMeasure_map_frestrictLe μ₀ κ
  · intro ν hν
    rcases hν with ⟨_, hν⟩
    exact IsProjectiveLimit.unique (hlimit hν) (hlimit (trajMeasure_map_frestrictLe μ₀ κ))

end

section

variable {X : ℕ → Type u}
variable [∀ n, MeasurableSpace (X n)]

-- Proof sketch: evaluate the finite-dimensional marginal identity from
-- `existsUnique_probability_measure_with_prescribed_finite_dimensional_marginals` on a measurable
-- set `s`, and rewrite the left-hand side with `Measure.map_apply` for the cylinder
-- `cylinder (Iic n) s`.
/-- The canonical Ionescu-Tulcea trajectory measure evaluates a measurable cylinder over the first
`n + 1` coordinates by the corresponding finite-dimensional iterated law. -/
theorem trajMeasure_apply_cylinder
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) {s : Set (Π i : Iic n, X i)} (hs : MeasurableSet s) :
    trajMeasure μ₀ κ (cylinder (Iic n) s) =
      (partialTraj κ 0 n ∘ₘ μ₀.map (piUnique (fun i : Iic 0 ↦ X i)).symm) s := by
  rw [← trajMeasure_map_frestrictLe μ₀ κ n, Measure.map_apply (measurable_frestrictLe n) hs]
  rfl

end

end ProbabilityTheory.Kernel
