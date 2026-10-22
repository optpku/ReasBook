/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_3
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_1

-- Declarations for this item will be appended below by the statement pipeline.

universe v

open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}

/- Definition 14.2 is `source-facing`: it introduces coordinate-wise minimality for a finite block
product.

Domain sampling against the local block-coordinate API identifies the owner split:
- `core/canonical`: Mathlib's `IsMinOn` owner for one-block slice minimizers;
- `core/canonical`: Chapter 14's `alternating_minimization_block_objective`, specialized to the
  fixed-base case `xNext = xStar`, for the one-block slice itself; and
- `bridge/view`: one-block replacement through `Function.update`, and, in `PiLp 2 Ei`, the
  additive singleton presentation `x + 𝒰[i] d` of the same replacement.

The primitive data are therefore only effective-domain membership and the per-block `IsMinOn`
conditions for the canonical Chapter 14 block objective. Pointwise comparison inequalities and the
additive singleton formula are derived API, not primitive public data. -/
/-- Definition 14.2: a point `xStar` is a coordinate-wise minimum of `F` on the finite block
product if `xStar ∈ dom(F)` and, for every block `i`, the current coordinate `xStar i`
globally minimizes the fixed-base Chapter 14 one-block objective obtained by varying only block
`i`. The additive perturbation formula `xStar + 𝒰[i] d` is the equivalent bridge view in
`PiLp 2 Ei`. -/
@[mk_iff is_coordinatewise_minimum_iff]
class is_coordinatewise_minimum
    (F : ((i : Fin p) → Ei i) → EReal) (xStar : (i : Fin p) → Ei i) : Prop where
  /-- A coordinate-wise minimum lies in the effective domain of the objective. -/
  mem_effective_domain : xStar ∈ effective_domain F
  /-- At a coordinate-wise minimum, each coordinate globally minimizes the fixed-base one-block
  slice. -/
  isMinOn (i : Fin p) :
    IsMinOn (alternating_minimization_block_objective F xStar xStar i) Set.univ (xStar i)

attribute [simp] is_coordinatewise_minimum.mem_effective_domain
attribute [simp] is_coordinatewise_minimum_iff

@[simp] theorem alternating_minimization_block_objective_base_self
    (F : ((i : Fin p) → Ei i) → EReal) (x : (i : Fin p) → Ei i) (i : Fin p) :
    alternating_minimization_block_objective F x x i (x i) = F x := by
  simp

/-- The coordinate-wise minimum owner exposes effective-domain membership to typeclass search. -/
instance instEffectiveDomainOfIsCoordinatewiseMinimum
    {F : ((i : Fin p) → Ei i) → EReal} {xStar : (i : Fin p) → Ei i}
    [h : is_coordinatewise_minimum F xStar] :
    xStar ∈ effective_domain F :=
  h.mem_effective_domain

/-- At a coordinate-wise minimum, every one-coordinate replacement has objective value at least
`F xStar`. -/
theorem is_coordinatewise_minimum.le_update
    {F : ((i : Fin p) → Ei i) → EReal} {xStar : (i : Fin p) → Ei i}
    (h : is_coordinatewise_minimum F xStar) (i : Fin p) (y : Ei i) :
    F xStar ≤ F (Function.update xStar i y) := by
  simpa [alternating_minimization_block_objective_base_apply] using
    (isMinOn_iff.mp (h.isMinOn i)) y (by simp)

end

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]

local notation "BlockSpace" => PiLp (2 : ENNReal) Ei

@[simp] theorem add_single_zero
    (x : BlockSpace) (i : Fin p) :
    x + 𝒰[i] (0 : Ei i) = x := by
  ext j
  by_cases h : j = i
  · subst h
    simp [PiLp.single_eq_same]
  · simp [h, PiLp.single_eq_of_ne]

/-- In `PiLp 2 Ei`, the fixed-base Chapter 14 one-block objective on the coordinate view agrees
with the additive singleton-update formula. -/
@[simp] theorem alternating_minimization_block_objective_toLp_eq_add_single
    (F : BlockSpace → EReal) (x : (i : Fin p) → Ei i) (i : Fin p) (y : Ei i) :
    alternating_minimization_block_objective (fun z ↦ F (WithLp.toLp 2 z)) x x i y =
      F (WithLp.toLp 2 x + 𝒰[i] (y - x i)) := by
  rw [alternating_minimization_block_objective_base_apply]
  congr 1
  ext j
  by_cases h : j = i
  · subst h
    simp [PiLp.single_eq_same]
  · simp [Function.update, h, PiLp.single_eq_of_ne]

/-- Bridge view: a coordinate-wise minimum of the coordinate pullback induces a one-block
`IsMinOn` statement for additive singleton perturbations in `PiLp 2 Ei`. -/
theorem is_coordinatewise_minimum.isMinOn_add_single
    {F : BlockSpace → EReal} {xStar : (i : Fin p) → Ei i}
    (h : is_coordinatewise_minimum (fun z ↦ F (WithLp.toLp 2 z)) xStar) (i : Fin p) :
    IsMinOn (fun y : Ei i ↦ F (WithLp.toLp 2 xStar + 𝒰[i] y)) Set.univ 0 := by
  rw [isMinOn_iff]
  intro y hy
  have hi := (isMinOn_iff.mp (h.isMinOn i)) (xStar i + y) (by simp)
  have hi' :
      F (WithLp.toLp 2 xStar) ≤
        F (WithLp.toLp 2 (Function.update xStar i (xStar i + y))) := by
    simpa [alternating_minimization_block_objective_base_apply] using hi
  have hupdate :
      WithLp.toLp 2 (Function.update xStar i (xStar i + y)) =
        WithLp.toLp 2 xStar + 𝒰[i] y := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [PiLp.single_eq_same]
    · simp [Function.update, hji, PiLp.single_eq_of_ne]
  simpa [hupdate] using hi'

/-- Bridge view: if the pullback of a `PiLp` objective along `WithLp.toLp 2` is coordinate-wise
minimal at `xStar`, then every one-block perturbation of `WithLp.toLp 2 xStar` has objective
value at least `F (WithLp.toLp 2 xStar)`. -/
theorem is_coordinatewise_minimum.le_add_single
    {F : BlockSpace → EReal} {xStar : (i : Fin p) → Ei i}
    (h : is_coordinatewise_minimum (fun z ↦ F (WithLp.toLp 2 z)) xStar)
    (i : Fin p) (y : Ei i) :
    F (WithLp.toLp 2 xStar) ≤ F (WithLp.toLp 2 xStar + 𝒰[i] y) := by
  have hy := (isMinOn_iff.mp (h.isMinOn_add_single i)) y (by simp)
  simpa using hy

end
