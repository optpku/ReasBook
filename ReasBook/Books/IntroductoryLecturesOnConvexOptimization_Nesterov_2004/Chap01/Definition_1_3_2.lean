/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/- Definition 1.3.2 is the source-facing owner for the textbook `ℓ∞` geometry on `ℝⁿ`.

Layer targeted by this refinement:
* source-facing owner `EuclideanSpace.linftyNorm n : EuclideanSpace ℝ (Fin n) → ℝ`
* core/canonical owner `EuclideanSpace.linftySeminorm n : Seminorm ℝ E`

Primary domain:
* finite-dimensional normed linear algebra on coordinate spaces

Sampled owner-style declarations:
* `normSeminorm ℝ (Fin n → ℝ)` for the canonical seminorm owner attached to the sup norm on
  coordinates
* `Pi.norm_def` for the canonical sup-norm formula on `Fin n → ℝ`
* `EuclideanSpace.equiv (Fin n) ℝ` for the coordinate view of `EuclideanSpace ℝ (Fin n)`
* `Seminorm.closedBall` together with `Seminorm.mem_closedBall_zero` for the canonical
  origin-centered ball API attached to a seminorm

Owner abstraction:
* source-facing owner: `EuclideanSpace.linftyNorm n : E → ℝ`
* core/canonical owner: `EuclideanSpace.linftySeminorm n : Seminorm ℝ E`
* lower-level canonical pullback: `normSeminorm ℝ Coord`

Source/core/bridge triage:
* source-facing: the textbook `ℓ∞` norm on `ℝⁿ`, exposed as `EuclideanSpace.linftyNorm`
* core/canonical: the seminorm owner `EuclideanSpace.linftySeminorm`
* bridge/view: the coordinate transport `x ↦ coordEquiv x` from `E` to `Coord`, the notation
  `‖x‖∞`, and the source-facing origin-centered ball `EuclideanSpace.linftyClosedBall r`

Primitive data:
* a vector `x : E`

Derived API:
* the evaluation notation `‖x‖∞ = EuclideanSpace.linftyNorm n x`
* the bridge `EuclideanSpace.linftyNorm n x = EuclideanSpace.linftySeminorm n x`
* the coordinate-owner bridge `‖x‖∞ = ‖coordEquiv x‖`
* the source-facing ball bridge
  `EuclideanSpace.linftyClosedBall r = (EuclideanSpace.linftySeminorm n).closedBall 0 r`
* the equivalent `WithLp ⊤` bridge `‖x‖∞ = ‖WithLp.toLp ⊤ (fun i ↦ x i)‖`
* the coordinate sup formula `‖x‖∞ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊)` from `Pi.norm_def`

This file keeps the source-facing textbook owner `EuclideanSpace.linftyNorm`, realized through the
canonical seminorm owner `EuclideanSpace.linftySeminorm`, so the chapter recall layer can use the
norm surface while downstream ball constructions still reuse `Seminorm.closedBall`. -/

namespace EuclideanSpace

private abbrev coordinateLinftyEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv

/-- Definition 1.3.2: the canonical coordinate `ℓ∞` seminorm on `ℝⁿ`, obtained by pulling back
the ordinary sup norm on `Fin n → ℝ` along the Euclidean coordinate linear equivalence. The
textbook `ℓ∞` norm is the derived source-facing owner `EuclideanSpace.linftyNorm`. -/
abbrev linftySeminorm (n : ℕ) : Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  Seminorm.comp (normSeminorm ℝ (Fin n → ℝ)) (coordinateLinftyEquiv n).toLinearMap

/-- Definition 1.3.2: the textbook `ℓ∞` norm on `ℝⁿ`. Its canonical implementation is the
evaluation of `EuclideanSpace.linftySeminorm`. -/
abbrev linftyNorm (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  linftySeminorm n

/-- The closed `ℓ∞`-ball of radius `r` centered at the origin in `ℝⁿ`. -/
abbrev linftyClosedBall {n : ℕ} (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (linftySeminorm n).closedBall 0 r

end EuclideanSpace

notation "‖" x "‖∞" => EuclideanSpace.linftyNorm _ x

@[simp] theorem linftyNorm_eq_linftySeminorm (x : E) :
    EuclideanSpace.linftyNorm n x = EuclideanSpace.linftySeminorm n x :=
  rfl

/-- Membership in the source-facing closed `ℓ∞`-ball is exactly the `ℓ∞`-norm bound. -/
@[simp] theorem mem_linftyClosedBall_iff {r : ℝ} {x : E} :
    x ∈ EuclideanSpace.linftyClosedBall r ↔ ‖x‖∞ ≤ r := by
    change x ∈ (EuclideanSpace.linftySeminorm n).closedBall 0 r ↔
      EuclideanSpace.linftyNorm n x ≤ r
    exact (EuclideanSpace.linftySeminorm n).mem_closedBall_zero

/-- The `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)` is the canonical sup norm on the coordinate owner
`Fin n → ℝ`. -/
@[simp] theorem linftyNorm_eq_coordNorm (x : E) :
    ‖x‖∞ = ‖coordEquiv x‖ :=
  by
    change ‖(EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv x‖ = ‖coordEquiv x‖
    rfl

/-- The source-facing `ℓ∞` norm agrees with the equivalent `WithLp ⊤` coordinate presentation. -/
@[simp] theorem linftyNorm_eq_toLp (x : E) :
    ‖x‖∞ = ‖WithLp.toLp ⊤ (fun i ↦ x i)‖ := by
  rw [linftyNorm_eq_coordNorm]
  change ‖coordEquiv x‖ = ‖WithLp.toLp ⊤ (coordEquiv x)‖
  rw [PiLp.norm_toLp]

/-- The source-facing `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)` is the coordinatewise sup norm. -/
theorem linftyNorm_eq_sup (x : E) :
    ‖x‖∞ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊) := by
  rw [linftyNorm_eq_coordNorm]
  simpa using (Pi.norm_def (coordEquiv x))
