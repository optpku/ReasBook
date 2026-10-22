/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory Topology

noncomputable section

namespace ProbabilityTheory

variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)

/-- Helper for Exercise 25.4.3: for positive radius, the frontier of the open ball is the sphere
of radius `|r|`. This support theorem isolates the `abs_of_pos` transport used repeatedly in the
item file. -/
theorem openBallFrontier_eq_sphereAbs
    (r : ℝ) (hr : 0 < r) :
    frontier (Metric.ball (0 : State) r) = Metric.sphere (0 : State) |r| := by
  -- Proof comment: `frontier_ball` gives the radius-`r` sphere, and positive radius removes the
  -- absolute value in the target spelling.
  simpa [abs_of_pos hr] using frontier_ball (0 : State) hr.ne'

/-- Helper for Exercise 25.4.3: the theorem-head transport from the frontier of the open ball to
the sphere of radius `|r|` is a standalone support definition. -/
noncomputable def openBallFrontierHomeomorphAbsSupport
    (r : ℝ) (hr : 0 < r) :
    frontier (Metric.ball (0 : State) r) ≃ₜ Metric.sphere (0 : State) |r| :=
  Homeomorph.setCongr (openBallFrontier_eq_sphereAbs (d := d) r hr)

/-- Helper for Exercise 25.4.3: the support homeomorphism is definitionally the `setCongr`
transport built from `openBallFrontier_eq_sphereAbs`. -/
@[simp] theorem openBallFrontierHomeomorphAbsSupport_apply
    (r : ℝ) (hr : 0 < r) (z : frontier (Metric.ball (0 : State) r)) :
    openBallFrontierHomeomorphAbsSupport (d := d) r hr z =
      (Homeomorph.setCongr (openBallFrontier_eq_sphereAbs (d := d) r hr)) z := by
  -- Proof comment: this is just the evaluation of the support definition.
  rfl

end ProbabilityTheory
