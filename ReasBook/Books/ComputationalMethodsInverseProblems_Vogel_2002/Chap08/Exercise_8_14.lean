/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1.Blur2D
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_1.Clauses
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_2.Clauses
public import Mathlib.LinearAlgebra.Matrix.Vec

public section

open scoped Matrix

/-!
Exercise 8.14.

The source asks for the Section `8.3.2` two-dimensional total-variation test
problem to be implemented with both steepest descent and Newton and for the
resulting runs to be compared by convergence rate and computational cost.

The Chapter 8 method clauses are now publicized as the source-facing owners
`TVSteepestDescent` and `TVNewton` in
`Book.Ch8.Algorithm_8_2_1.Clauses` and `Book.Ch8.Algorithm_8_2_2.Clauses`.
What this exercise needs at the source-facing level is therefore the Chapter 5
sampled benchmark datum `Blur2D.sampledObservedImage` together with the
benchmark-specialized steepest-descent and Newton run surfaces.

The source also asks the resulting runs to be compared by convergence rate and
computational cost. The current repository snapshot still does not provide
canonical Chapter 8 owners for those comparison criteria, and introducing an
exercise-local comparison predicate with arbitrary external rate/cost parameters
would weaken the source meaning. Accordingly the comparison claim remains a
labeled blocker/check-only surface rather than a guessed public owner.
-/

namespace TwoDimensionalTVBenchmark

/-- Real `n_x × n_y` image arrays on the Section `8.3.2` grid. -/
abbrev ImageMatrix (n_x n_y : ℕ) := Matrix (Fin n_x) (Fin n_y) ℝ

/-- Column-stacked real images on the same grid, using the Chapter 5
`Matrix.vec` convention. -/
abbrev ImageVector (n_x n_y : ℕ) := Fin n_y × Fin n_x → ℝ

/-- The vectorized Section `8.3.2` datum obtained from the canonical Chapter 5
owner `Blur2D.sampledObservedImage` and used by the discrete Chapter 8
least-squares terms. -/
def observedDatumVec {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ)
    (fTrue η : ImageMatrix n_x n_y) : ImageVector n_x n_y :=
  (Blur2D.sampledObservedImage k Δx Δy xcoord ycoord fTrue η).vec

/-- `IsSteepestDescentRun` specializes the clause surface of
`Book.Ch8.Algorithm_8_2_1` to the Section `8.3.2` benchmark datum. -/
def IsSteepestDescentRun {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ)
    (fTrue η : ImageMatrix n_x n_y)
    (K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (α : ℝ)
    (T : ImageVector n_x n_y → ℝ)
    (f0 : ImageVector n_x n_y)
    (f g : ℕ → ImageVector n_x n_y)
    (τ : ℕ → ℝ) : Prop :=
  TVSteepestDescent.IsInitialized f0 f ∧
    TVSteepestDescent.HasGradientFormula
      K (observedDatumVec k Δx Δy xcoord ycoord fTrue η) L α f g ∧
    TVSteepestDescent.HasExactLineSearch T f g τ ∧
    TVSteepestDescent.HasIterateUpdate f g τ

theorem IsSteepestDescentRun.init_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g : ℕ → ImageVector n_x n_y}
    {τ : ℕ → ℝ}
    (h : IsSteepestDescentRun
      k Δx Δy xcoord ycoord fTrue η K L α T f0 f g τ) :
    f 0 = f0 :=
  h.1

theorem IsSteepestDescentRun.gradient_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g : ℕ → ImageVector n_x n_y}
    {τ : ℕ → ℝ}
    (h : IsSteepestDescentRun
      k Δx Δy xcoord ycoord fTrue η K L α T f0 f g τ)
    (v : ℕ) :
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) -
        observedDatumVec k Δx Δy xcoord ycoord fTrue η) +
        α • Matrix.mulVec (L (f v)) (f v) :=
  h.2.1 v

theorem IsSteepestDescentRun.lineSearch {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g : ℕ → ImageVector n_x n_y}
    {τ : ℕ → ℝ}
    (h : IsSteepestDescentRun
      k Δx Δy xcoord ycoord fTrue η K L α T f0 f g τ)
    (v : ℕ) :
    IsMinOn (LineSearch.profile T (f v) (-g v)) (Set.Ioi (0 : ℝ)) (τ v) :=
  h.2.2.1 v

theorem IsSteepestDescentRun.iterate_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g : ℕ → ImageVector n_x n_y}
    {τ : ℕ → ℝ}
    (h : IsSteepestDescentRun
      k Δx Δy xcoord ycoord fTrue η K L α T f0 f g τ)
    (v : ℕ) :
    f (v + 1) = f v - τ v • g v :=
  h.2.2.2 v

/-- `IsNewtonRun` specializes the clause surface of
`Book.Ch8.Algorithm_8_2_2` to the Section `8.3.2` benchmark datum. -/
def IsNewtonRun {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ)
    (fTrue η : ImageMatrix n_x n_y)
    (K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (α : ℝ)
    (T : ImageVector n_x n_y → ℝ)
    (f0 : ImageVector n_x n_y)
    (f g s : ℕ → ImageVector n_x n_y)
    (HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (τ : ℕ → ℝ) : Prop :=
  TVNewton.IsInitialized f0 f ∧
    TVNewton.HasGradientAndPenaltyHessian
      K (observedDatumVec k Δx Δy xcoord ycoord fTrue η) α L L' f g HJ ∧
    TVNewton.HasHessianAndNewtonStep K α g s HJ H ∧
    TVNewton.HasLineSearchAndIterateUpdate T f s τ

theorem IsNewtonRun.init_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ) :
    f 0 = f0 :=
  h.1

theorem IsNewtonRun.gradient_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ)
    (v : ℕ) :
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) -
        observedDatumVec k Δx Δy xcoord ycoord fTrue η) +
        α • Matrix.mulVec (L (f v)) (f v) :=
  TVNewton.HasGradientAndPenaltyHessian.gradient_eq h.2.1 v

theorem IsNewtonRun.penaltyHessian_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ)
    (v : ℕ) :
    HJ v = L (f v) + L' (f v) (f v) :=
  (h.2.1 v).2

theorem IsNewtonRun.hessian_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ)
    (v : ℕ) :
    H v = Kᵀ * K + α • HJ v :=
  (h.2.2.1 v).1

theorem IsNewtonRun.newtonStep_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ)
    (v : ℕ) :
    s v = -Matrix.mulVec ((H v)⁻¹) (g v) :=
  (h.2.2.1 v).2

theorem IsNewtonRun.lineSearch {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ)
    (v : ℕ) :
    IsMinOn (LineSearch.profile T (f v) (s v)) (Set.Ioi (0 : ℝ)) (τ v) :=
  (h.2.2.2 v).1

theorem IsNewtonRun.iterate_eq {n_x n_y : ℕ}
    {k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ}
    {Δx Δy : ℝ}
    {xcoord : Fin n_x → ℝ}
    {ycoord : Fin n_y → ℝ}
    {fTrue η : ImageMatrix n_x n_y}
    {K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L : ImageVector n_x n_y → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {L' :
      ImageVector n_x n_y →
        ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {α : ℝ}
    {T : ImageVector n_x n_y → ℝ}
    {f0 : ImageVector n_x n_y}
    {f g s : ℕ → ImageVector n_x n_y}
    {HJ H : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    {τ : ℕ → ℝ}
    (h : IsNewtonRun
      k Δx Δy xcoord ycoord fTrue η K L L' α T f0 f g s HJ H τ)
    (v : ℕ) :
    f (v + 1) = f v + τ v • s v :=
  (h.2.2.2 v).2

end TwoDimensionalTVBenchmark

/- Exercise 8.14. The concrete sampled datum of the Section `8.3.2`
two-dimensional benchmark is the Chapter 5 owner `Blur2D.sampledObservedImage`. -/
#check Blur2D.sampledObservedImage

/- Exercise 8.14. The vectorized benchmark datum used by the discrete Chapter 8
least-squares terms. -/
#check TwoDimensionalTVBenchmark.observedDatumVec

/- Exercise 8.14. The benchmark-specialized steepest-descent surface. -/
#check TwoDimensionalTVBenchmark.IsSteepestDescentRun

/- Exercise 8.14. The benchmark-specialized Newton surface. -/
#check TwoDimensionalTVBenchmark.IsNewtonRun

/- Exercise 8.14. Main labeled source-facing blocker entry.

The benchmark-specialized steepest-descent and Newton run surfaces are
formalized above. The source's convergence-rate and computational-cost
comparison still depends on missing canonical Chapter 8 comparison owners, so
the exercise-level comparison claim remains check-only instead of being
weakened to an arbitrary external predicate. -/
#check
  fun {n_x n_y : ℕ}
    (k : (ℝ × ℝ) → (ℝ × ℝ) → ℝ)
    (Δx Δy : ℝ)
    (xcoord : Fin n_x → ℝ)
    (ycoord : Fin n_y → ℝ)
    (fTrue η : TwoDimensionalTVBenchmark.ImageMatrix n_x n_y)
    (K : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (L :
      TwoDimensionalTVBenchmark.ImageVector n_x n_y →
        Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (L' :
      TwoDimensionalTVBenchmark.ImageVector n_x n_y →
        TwoDimensionalTVBenchmark.ImageVector n_x n_y →
          Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (α : ℝ)
    (T : TwoDimensionalTVBenchmark.ImageVector n_x n_y → ℝ)
    (f0 : TwoDimensionalTVBenchmark.ImageVector n_x n_y)
    (fSteepest gSteepest : ℕ → TwoDimensionalTVBenchmark.ImageVector n_x n_y)
    (τSteepest : ℕ → ℝ)
    (fNewton gNewton sNewton : ℕ → TwoDimensionalTVBenchmark.ImageVector n_x n_y)
    (HJNewton HNewton : ℕ →
      Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (τNewton : ℕ → ℝ) ↦
      TwoDimensionalTVBenchmark.IsSteepestDescentRun
          k Δx Δy xcoord ycoord fTrue η K L α T f0
          fSteepest gSteepest τSteepest ∧
        TwoDimensionalTVBenchmark.IsNewtonRun
          k Δx Δy xcoord ycoord fTrue η K L L' α T f0
          fNewton gNewton sNewton HJNewton HNewton τNewton
