/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1.Polyhedron
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Closure
open scoped Matrix

variable {m n : ℕ}

/-- A simplified exact ellipsoid state in `ℝ^n`, recording the center queried by the algorithm
and the carrier set used in the containment and volume arguments. -/
structure RealEllipsoid (n : ℕ) where
  /-- The center of the ellipsoid. -/
  center : Fin n → ℝ
  /-- The subset of `ℝ^n` represented by the current ellipsoid state. -/
  carrier : Set (Fin n → ℝ)

/-- `E'` contains the part of `E` satisfying row `i` of the rational system `(A, b)`. The
polynomial-cutoff proof tracks the separate volume-shrink hypothesis independently. -/
def IsMinimumVolumeCutUpdate
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (i : Fin m)
    (E E' : RealEllipsoid n) : Prop :=
  let cut := E.carrier ∩
    {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)}
  cut ⊆ E'.carrier

/-- A tagged feasibility output is either a candidate feasible point or the empty-interior
outcome of the ellipsoid algorithm. -/
inductive EllipsoidFeasibilityOutput (n : ℕ) : Type
  /-- A point returned as feasible. -/
  | feasiblePoint (x : Fin n → ℝ)
  /-- The algorithm reports that the polyhedron has empty interior. -/
  | emptyInterior

namespace EllipsoidFeasibilityOutput

/-- A tagged output is correct for `(A, b)` when its point is feasible or its empty-interior tag
states the actual topological conclusion. -/
def IsCorrect
    (output : EllipsoidFeasibilityOutput n)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Prop :=
  match output with
  | .feasiblePoint x => x ∈ rational_matrix_polyhedron A b
  | .emptyInterior => interior (rational_matrix_polyhedron A b) = ∅

end EllipsoidFeasibilityOutput

/-- An initial ellipsoid is valid for `(A, b)` when it contains the represented polyhedron. -/
def IsValidEllipsoidInitialization
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (E₀ : RealEllipsoid n) : Prop :=
  rational_matrix_polyhedron A b ⊆ E₀.carrier

/-- One operational step of the exact ellipsoid algorithm returns a feasible point, certifies
empty interior, or records a violated row and the next ellipsoid. Exhausting the chosen cutoff
also produces the empty-interior output. -/
inductive EllipsoidAlgorithmStep (m n : ℕ) : Type
  /-- The algorithm terminates with the displayed feasible point. -/
  | feasiblePoint (x : Fin n → ℝ)
  /-- The algorithm terminates early with a certified empty-interior outcome. -/
  | emptyInterior
  /-- The algorithm continues using row `i` and the displayed next ellipsoid. -/
  | next (i : Fin m) (E' : RealEllipsoid n)

namespace EllipsoidAlgorithmStep

/-- A step is valid at `E` when a feasible output is correct, an empty-interior output has a
state-local empty-cut certificate, or a continuation uses a genuinely violated row and the
required minimum-volume update. -/
def IsValidAt
    (step : EllipsoidAlgorithmStep m n)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (E : RealEllipsoid n) : Prop :=
  match step with
  | .feasiblePoint x => x = E.center ∧ x ∈ rational_matrix_polyhedron A b
  | .emptyInterior =>
      ∃ i : Fin m,
        (b i : ℝ) < ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ E.center ∧
          interior (E.carrier ∩
            {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)}) = ∅
  | .next i E' =>
      (b i : ℝ) < ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ E.center ∧
        IsMinimumVolumeCutUpdate A b i E E'

/-- A state-local empty-cut certificate gives a correct empty-interior output whenever the
current ellipsoid still contains the represented polyhedron. -/
theorem emptyInterior_isCorrect
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (E : RealEllipsoid n)
    (h_step : (EllipsoidAlgorithmStep.emptyInterior : EllipsoidAlgorithmStep m n).IsValidAt A b E)
    (h_initial : IsValidEllipsoidInitialization A b E) :
    (EllipsoidFeasibilityOutput.emptyInterior : EllipsoidFeasibilityOutput n).IsCorrect A b := by
  -- Route correction: use the canonical topology/interior API on `Fin n → ℝ` from imports,
  -- then transfer the empty-cut certificate back to the polyhedron by `interior_mono`.
  -- The local empty-cut certificate contains the whole polyhedron, so its interior is empty.
  rcases
      (show
          ∃ i : Fin m,
            (b i : ℝ) < ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ E.center ∧
              interior (E.carrier ∩
                {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)}) = ∅ by
        simpa [EllipsoidAlgorithmStep.IsValidAt] using h_step) with
    ⟨i, _, h_emptyCut⟩
  have h_initial_subset : rational_matrix_polyhedron A b ⊆ E.carrier := by
    simpa [IsValidEllipsoidInitialization] using h_initial
  have h_polyhedron_subset :
      rational_matrix_polyhedron A b ⊆
        E.carrier ∩
          {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)} := by
    intro x hx_polyhedron
    refine ⟨h_initial_subset hx_polyhedron, ?_⟩
    rw [mem_rational_matrix_polyhedron] at hx_polyhedron
    exact hx_polyhedron i
  have h_interior_subset :
      interior (rational_matrix_polyhedron A b) ⊆
        interior
          (E.carrier ∩
            {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)}) :=
    interior_mono h_polyhedron_subset
  have h_emptyInterior : interior (rational_matrix_polyhedron A b) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx_cut :
        x ∈ interior
          (E.carrier ∩
            {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)}) :=
      h_interior_subset hx
    rw [h_emptyCut] at hx_cut
    exact hx_cut
  simpa [EllipsoidFeasibilityOutput.IsCorrect] using h_emptyInterior

end EllipsoidAlgorithmStep

/-- A terminal-aware exact ellipsoid execution for `(A, b)` from `E₀`. Its state-local
operational law is required only at ellipsoids that still contain the represented polyhedron. -/
structure EllipsoidAlgorithm
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (E₀ : RealEllipsoid n) where
  /-- The next operational step at the current ellipsoid. -/
  step : RealEllipsoid n → EllipsoidAlgorithmStep m n
  /-- On a valid current ellipsoid, the chosen step has a locally certified terminal result or
  follows the exact minimum-volume cut recurrence. -/
  step_valid : ∀ E : RealEllipsoid n, IsValidEllipsoidInitialization A b E →
    (step E).IsValidAt A b E

namespace EllipsoidAlgorithm

/-- Build a terminal-aware execution from an explicit step function satisfying its validity law
on admissible initialized ellipsoids. -/
def ofSteps
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} {E₀ : RealEllipsoid n}
    (step : RealEllipsoid n → EllipsoidAlgorithmStep m n)
    (step_valid : ∀ E : RealEllipsoid n, IsValidEllipsoidInitialization A b E →
      (step E).IsValidAt A b E) :
    EllipsoidAlgorithm A b E₀ :=
  { step := step
    step_valid := step_valid }

/-- Execute the exact ellipsoid algorithm until it finds a feasible center or exhausts the
chosen cutoff; cutoff exhaustion returns the empty-interior outcome. -/
def runFor
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} {E₀ : RealEllipsoid n}
    (algorithm : EllipsoidAlgorithm A b E₀) :
    ℕ → RealEllipsoid n → EllipsoidFeasibilityOutput n
  | 0, _ => .emptyInterior
  | t + 1, E =>
      match algorithm.step E with
      | .feasiblePoint x => .feasiblePoint x
      | .emptyInterior => .emptyInterior
      | .next _ E' => algorithm.runFor t E'

/-- The algorithm has a correct output by `tStar` when its fuelled execution emits a tagged
output that is correct for the rational system. -/
def correctOutputBy
    {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ} {E₀ : RealEllipsoid n}
    (algorithm : EllipsoidAlgorithm A b E₀) (tStar : ℕ) : Prop :=
  (algorithm.runFor tStar E₀).IsCorrect A b

end EllipsoidAlgorithm

/-- A uniform ellipsoid algorithm selects one terminal-aware execution for every rational linear
system and initial ellipsoid. -/
structure UniformEllipsoidAlgorithm where
  /-- The terminal-aware execution selected from the system and its initial ellipsoid. -/
  run : ∀ {m n : ℕ}, (A : Matrix (Fin m) (Fin n) ℚ) → (b : Fin m → ℚ) →
    (E₀ : RealEllipsoid n) → EllipsoidAlgorithm A b E₀

namespace UniformEllipsoidAlgorithm

/-- Build a uniform algorithm from an explicit family of terminal-aware executions. -/
def ofRuns
    (run : ∀ {m n : ℕ}, (A : Matrix (Fin m) (Fin n) ℚ) → (b : Fin m → ℚ) →
      (E₀ : RealEllipsoid n) → EllipsoidAlgorithm A b E₀) :
    UniformEllipsoidAlgorithm :=
  { run := run }

end UniformEllipsoidAlgorithm
