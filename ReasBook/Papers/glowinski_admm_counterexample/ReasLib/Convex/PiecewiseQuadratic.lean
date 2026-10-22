/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Convex.Polyhedral
public import Mathlib.Analysis.Convex.Function

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

/-- A real objective that is convex with closed epigraph and agrees on a finite
polyhedral cover with explicit continuous quadratic-affine formulas. -/
def IsFiniteClosedConvexPiecewiseQuadratic {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧
    IsClosed {p : E × ℝ | f p.1 ≤ p.2} ∧
    ∃ n : ℕ, ∃ cells : Fin n → Set E,
      ∃ q : Fin n → E →L[ℝ] E, ∃ l : Fin n → E, ∃ c : Fin n → ℝ,
        (∀ z, ∃ i, z ∈ cells i) ∧
        ∀ i, IsPolyhedralSet (cells i) ∧
          ∀ z ∈ cells i, f z = inner ℝ (q i z) z / 2 + inner ℝ (l i) z + c i

/-- The piecewise-quadratic predicate exposes convexity, closed epigraph, and
its finite polyhedral quadratic presentation. -/
theorem finiteClosedConvexPiecewiseQuadratic_iff {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} :
    IsFiniteClosedConvexPiecewiseQuadratic f ↔
      ConvexOn ℝ Set.univ f ∧
        IsClosed {p : E × ℝ | f p.1 ≤ p.2} ∧
        ∃ n : ℕ, ∃ cells : Fin n → Set E,
          ∃ q : Fin n → E →L[ℝ] E, ∃ l : Fin n → E, ∃ c : Fin n → ℝ,
            (∀ z, ∃ i, z ∈ cells i) ∧
            ∀ i, IsPolyhedralSet (cells i) ∧
              ∀ z ∈ cells i,
                f z = inner ℝ (q i z) z / 2 + inner ℝ (l i) z + c i := by
  -- Unfolding the predicate leaves the displayed presentation on both sides.
  rfl

end ConsensusADMM
