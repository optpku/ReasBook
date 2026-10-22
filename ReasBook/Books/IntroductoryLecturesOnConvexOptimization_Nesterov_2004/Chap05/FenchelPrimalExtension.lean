/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u}

local instance {p : Prop} : Decidable p := Classical.propDecidable p

/- Chapter 5 repeatedly extends a real-valued function by `+∞` away from a feasible set. The
generic owner for that construction is independent of later Fenchel-duality arguments, so it
lives in this small support file rather than inside a downstream theorem file. -/

/-- The `WithTop ℝ`-valued extension of a real-valued function `f` by `+∞` outside the feasible
set `Q`. -/
def fenchelPrimalExtension (Q : Set E) (f : E → ℝ) : E → WithTop ℝ :=
  fun x ↦ if x ∈ Q then (f x : WithTop ℝ) else ⊤

/-- On `Q`, `fenchelPrimalExtension Q f` agrees with the original real-valued function `f`. -/
@[simp] theorem fenchelPrimalExtension_apply_of_mem {Q : Set E} {f : E → ℝ} {x : E}
    (hx : x ∈ Q) :
    fenchelPrimalExtension Q f x = (f x : WithTop ℝ) := by
  classical
  simp [fenchelPrimalExtension, hx]

@[simp] theorem fenchelPrimalExtension_apply_of_not_mem {Q : Set E} {f : E → ℝ} {x : E}
    (hx : x ∉ Q) :
    fenchelPrimalExtension Q f x = ⊤ := by
  classical
  simp [fenchelPrimalExtension, hx]

/-- The effective domain of `fenchelPrimalExtension Q f` is exactly the feasible set `Q`. -/
@[simp] theorem mem_dom_fenchelPrimalExtension_iff {Q : Set E} {f : E → ℝ} {x : E} :
    x ∈ dom (fenchelPrimalExtension Q f) ↔ x ∈ Q := by
  constructor
  · intro hx
    by_contra hQ
    simp [fenchelPrimalExtension_apply_of_not_mem hQ] at hx
  · intro hx
    simp [fenchelPrimalExtension_apply_of_mem hx]

/-- The canonical effective domain of the `+∞`-extension is the original feasible set. -/
@[simp] theorem dom_fenchelPrimalExtension {Q : Set E} {f : E → ℝ} :
    dom (fenchelPrimalExtension Q f) = Q := by
  ext x
  exact mem_dom_fenchelPrimalExtension_iff

/-- On the effective domain, the finite real part of `fenchelPrimalExtension Q f` is just `f`. -/
@[simp] theorem withTopRealPart_fenchelPrimalExtension_apply_of_mem
    {Q : Set E} {f : E → ℝ} {x : E} (hx : x ∈ Q) :
    withTopRealPart (fenchelPrimalExtension Q f) x = f x := by
  classical
  simp [fenchelPrimalExtension, withTopRealPart, hx]

end
