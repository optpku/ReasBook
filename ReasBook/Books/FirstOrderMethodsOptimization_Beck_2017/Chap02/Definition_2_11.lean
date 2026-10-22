/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SMul ℝ E] {S : Set E}

/-- Definition 2.11: A subset is a cone if it is closed under multiplication by nonnegative real
scalars. -/
def IsCone (S : Set E) : Prop :=
  ∀ ⦃a : NNReal⦄ ⦃x : E⦄, x ∈ S → a • x ∈ S

/-- A cone carries the canonical bundled `NNReal`-subaction on its underlying set. -/
def IsCone.toSubMulAction (hS : IsCone S) : SubMulAction NNReal E where
  carrier := S
  smul_mem' := fun _ _ hx ↦ hS hx

@[simp] theorem mem_toSubMulAction (hS : IsCone S) {x : E} :
    x ∈ hS.toSubMulAction ↔ x ∈ S :=
  Iff.rfl

-- Proof sketch: reinterpret nonnegative real scalars as `ℝ≥0` and use `NNReal.smul_def` to pass
-- between the canonical restricted scalar action and the textbook `0 ≤ a` formulation.
/-- A set is a cone exactly when every nonnegative scalar multiple of each of its points remains
in the set. -/
theorem isCone_iff_smul_mem :
    IsCone S ↔ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : E⦄, x ∈ S → a • x ∈ S := by
  constructor
  · intro hS a ha x hx
    change ((⟨a, ha⟩ : NNReal) • x) ∈ S
    exact hS hx
  · intro hS
    rintro ⟨a, ha⟩ x hx
    simpa [NNReal.smul_def] using hS ha hx
