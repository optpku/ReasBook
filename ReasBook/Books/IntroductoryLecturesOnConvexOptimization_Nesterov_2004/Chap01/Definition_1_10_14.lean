/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

open Set

universe u

-- Declarations for this item will be appended below by the statement pipeline.

variable {E : Type u} [TopologicalSpace E]

/- Primary domain: continuous real-valued maps that detect a subset through their zero set.

Sampled owner-style declarations:
* `C(E, ℝ)`, the canonical owner for continuous real-valued maps;
* `Set.EqOn`, the canonical localized equality predicate for functions on a set;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, the nearby chapter owner predicate on a
  bundled continuous map;
* `ContDiffMapSupportedIn.zero_on_compl` in mathlib, a nearby owner property organized around a
  vanishing condition rather than extra wrapper data.

Best owner abstraction:
* source-facing: `IsPenaltyFunction F Phi`;
* core/canonical: the bundled continuous map `Phi : C(E, ℝ)`;
* bridge/view: the exact zero-locus identity `F = Phi ⁻¹' {0}` and its pointwise reformulations.

Primitive data:
* `Phi` is globally nonnegative;
* the exact zero-locus identity `F = Phi ⁻¹' {0}`.

Derived API:
* the pointwise characterizations `x ∈ F ↔ Phi x = 0` and `Phi x = 0 ↔ x ∈ F`;
* `EqOn Phi 0 F`;
* strict positivity on `Fᶜ`;
* closedness of `F`.

The source phrase "closed set" is therefore redundant here: once the zero set is part of the owner
data, closedness follows immediately from continuity. -/

/-- Definition 1.10.14: for a set `F` in the ambient space, a continuous real-valued map is a
penalty function for `F` if it is nonnegative and vanishes exactly on `F`. The customary
strict-positivity statement on the complement is derived API. -/
class IsPenaltyFunction (F : Set E) (Phi : C(E, ℝ)) : Prop where
  nonneg (x : E) : 0 ≤ Phi x
  zeroSet_eq : F = Phi ⁻¹' ({0} : Set ℝ)

namespace IsPenaltyFunction

variable {F : Set E} {Phi : C(E, ℝ)}

/-- A penalty function vanishes exactly on the underlying set. -/
theorem mem_iff_eq_zero (hPhi : IsPenaltyFunction F Phi) {x : E} :
    x ∈ F ↔ Phi x = 0 := by
  rw [hPhi.zeroSet_eq]
  simp

/-- The defining zero-locus condition can also be read in the codomain-to-domain direction. -/
theorem eq_zero_iff_mem (hPhi : IsPenaltyFunction F Phi) {x : E} :
    Phi x = 0 ↔ x ∈ F := by
  simpa using hPhi.mem_iff_eq_zero.symm

/-- A penalty function vanishes on the underlying set. -/
theorem eqOn_zero (hPhi : IsPenaltyFunction F Phi) : EqOn Phi 0 F := by
  intro x hx
  simpa using hPhi.mem_iff_eq_zero.mp hx

/-- A penalty function is strictly positive on the complement of its zero set. -/
theorem pos_of_notMem (hPhi : IsPenaltyFunction F Phi) {x : E} (hx : x ∉ F) :
    0 < Phi x := by
  have hne : Phi x ≠ 0 := by
    intro hx0
    exact hx (hPhi.mem_iff_eq_zero.mpr hx0)
  exact lt_of_le_of_ne (hPhi.nonneg x) (by simpa [eq_comm] using hne)

/-- The zero set of a penalty function is closed, so the underlying set is automatically closed. -/
theorem isClosed (hPhi : IsPenaltyFunction F Phi) : IsClosed F := by
  rw [hPhi.zeroSet_eq]
  exact isClosed_singleton.preimage Phi.continuous

end IsPenaltyFunction

/-- A penalty-function hypothesis canonically supplies the owner-level vanishing condition on its
underlying set. -/
instance {F : Set E} {Phi : C(E, ℝ)} [hPhi : IsPenaltyFunction F Phi] : Fact (EqOn Phi 0 F) :=
  ⟨hPhi.eqOn_zero⟩
