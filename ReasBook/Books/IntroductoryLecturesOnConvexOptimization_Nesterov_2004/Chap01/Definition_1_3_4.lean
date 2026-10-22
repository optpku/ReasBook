/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ
local notation "coordBox" => (Set.Icc (0 : Coord) 1)

/- Definition 1.3.4 is a source-facing recall of the chapter's canonical box-Lipschitz owner API.

Layer targeted by this refinement:
* source-facing owner of the textbook class `𝒫∞[n, L]`
* bridge/view to the core/canonical owner predicate already used downstream in Chapter 1

Primary domain:
* Lipschitz continuity on finite-dimensional coordinate cubes

Sampled owner-style declarations:
* `LipschitzOnWith` in mathlib, the owner predicate for a Lipschitz bound on a set
* `lipschitzOnWith_iff_dist_le_mul` in mathlib, the canonical pointwise inequality view
* `EuclideanSpace.linftyNorm` in `Definition_1_3_2.lean`, the source-facing `ℓ∞` norm on
  `EuclideanSpace ℝ (Fin n)`
* `EuclideanSpace.equiv (Fin n) ℝ`, the coordinate transport from `EuclideanSpace ℝ (Fin n)` to
  `Fin n → ℝ`
* `zeroOneBox` and `mem_zeroOneBox_iff` in `Definition_1_3_1.lean`, the source-facing box and
  its coordinate-membership bridge

Source/core/bridge triage:
* source-facing: the textbook class `𝒫∞[n, L]` of objectives that are `L`-Lipschitz on
  `B_n = [0,1]^n` in the `ℓ∞` geometry
* core/canonical: `LipschitzOnWith L g Q`
* bridge/view: transport of `f` and `B_n` along `coordEquiv`, giving the coordinate owner set
  `coordBox = Set.Icc (0 : Coord) 1`

Owner abstraction:
* `linftyLipschitzClass n L`
* notation surface `𝒫∞[n, L]`
* canonical bridge
  `f ∈ 𝒫∞[n, L] ↔ LipschitzOnWith L (f ∘ coordEquiv.symm) coordBox`

Primitive data:
* a Lipschitz constant `L`
* an objective `f : E → ℝ`

Derived API:
* the definitional textbook `ℓ∞` inequality
  `|f x - f y| ≤ (L : ℝ) * ‖x - y‖∞`
  for `x, y ∈ zeroOneBox n`
* the bridge to the canonical coordinate predicate `LipschitzOnWith`
* the source-facing box membership criterion from `mem_zeroOneBox_iff`

This file keeps `LipschitzOnWith` only as a bridge to the coordinate owner predicate. The public
Chapter 1 surface is the source-facing class `𝒫∞[n, L]` on objectives `E → ℝ`, so downstream
files do not recreate `coordEquiv` and `coordBox` just to state admissibility. -/

/-- Definition 1.3.4: the textbook class `𝒫∞[n, L]` of objectives on `B_n = [0,1]^n` that are
`L`-Lipschitz in the `ℓ∞` geometry. Its primitive owner is the canonical coordinate-cube
predicate `LipschitzOnWith`. -/
def linftyLipschitzClass (n : ℕ) (L : NNReal) :
    Set (EuclideanSpace ℝ (Fin n) → ℝ) :=
  {f | LipschitzOnWith L (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
      (Set.Icc (0 : Fin n → ℝ) 1)}

notation "𝒫∞[" n ", " L "]" => linftyLipschitzClass n L

theorem mem_linftyLipschitzClass_iff_lipschitzOnWith {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔ LipschitzOnWith L (f ∘ (coordEquiv).symm) coordBox :=
  by
    change
      LipschitzOnWith L (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
          (Set.Icc (0 : Fin n → ℝ) 1) ↔
        LipschitzOnWith L (f ∘ (coordEquiv).symm) coordBox
    rfl

private theorem coordEquiv_mem_coordBox_iff {x : E} :
    coordEquiv x ∈ coordBox ↔ x ∈ zeroOneBox n := by
  constructor
  · intro hx i
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    exact ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩

/-- Membership in `𝒫∞[n, L]` is exactly the defining textbook `ℓ∞`-Lipschitz estimate on
`B_n = [0,1]^n`. -/
@[simp] theorem mem_linftyLipschitzClass_iff {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔
      ∀ x ∈ zeroOneBox n, ∀ y ∈ zeroOneBox n, |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞ := by
  rw [mem_linftyLipschitzClass_iff_lipschitzOnWith, lipschitzOnWith_iff_dist_le_mul]
  constructor
  · intro hf x hx y hy
    have hx' : coordEquiv x ∈ coordBox := by
      exact coordEquiv_mem_coordBox_iff.mpr hx
    have hy' : coordEquiv y ∈ coordBox := by
      exact coordEquiv_mem_coordBox_iff.mpr hy
    simpa [Function.comp, Real.dist_eq, linftyNorm_eq_coordNorm] using
      hf (coordEquiv x) hx' (coordEquiv y) hy'
  · intro hf x hx y hy
    let x' : E := (coordEquiv).symm x
    let y' : E := (coordEquiv).symm y
    have hx' : x' ∈ zeroOneBox n := by
      exact coordEquiv_mem_coordBox_iff.mp <| by
        simpa [x'] using hx
    have hy' : y' ∈ zeroOneBox n := by
      exact coordEquiv_mem_coordBox_iff.mp <| by
        simpa [y'] using hy
    simpa [Function.comp, Real.dist_eq, x', y', linftyNorm_eq_coordNorm] using hf x' hx' y' hy'

/-- The canonical owner predicate on the coordinate cube gives the textbook `ℓ∞`-Lipschitz
estimate on `B_n = [0,1]^n`. -/
theorem abs_sub_le_mul_linftyNorm
    {L : NNReal} {f : E → ℝ} (hf : f ∈ 𝒫∞[n, L])
    {x y : E} (hx : x ∈ zeroOneBox n) (hy : y ∈ zeroOneBox n) :
    |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞ := by
  exact mem_linftyLipschitzClass_iff.mp hf x hx y hy
