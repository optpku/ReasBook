/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory MeasurableEquiv Preorder ProbabilityTheory

universe u

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

/-- Remark 14.31: the finite experiment up to time `n` is the marginal of the canonical
trajectory measure on the first `n + 1` coordinates, hence agrees with the iterated law obtained
from the initial measure on `X 0` and the successive stochastic kernels `κ i`. -/
theorem trajMeasure_map_frestrictLe (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (trajMeasure μ₀ κ).map (frestrictLe n) =
      partialTraj κ 0 n ∘ₘ μ₀.map (piUnique (fun i : Iic 0 ↦ X i)).symm := by
  rw [trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe n), traj_map_frestrictLe]
  rfl

end ProbabilityTheory.Kernel
