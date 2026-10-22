/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Convex.ExtendedReal
public import glowinski_admm_counterexample.ReasLib.Convex.Polyhedral
public import glowinski_admm_counterexample.ReasLib.Convex.PiecewiseQuadratic

@[expose] public section

open scoped RealInnerProductSpace

universe u

/- Compatibility checks for the migrated extended-real objective API. -/
#check (ConsensusADMM.ofReal :
  ∀ {E : Type u}, (E → ℝ) → E → EReal)
#check (ConsensusADMM.ofReal_apply :
  ∀ {E : Type u} (f : E → ℝ) (x : E),
    ConsensusADMM.ofReal f x = (f x : EReal))
#check (ConsensusADMM.extendedIndicator :
  ∀ {E : Type u}, Set E → E → EReal)
#check (ConsensusADMM.extendedIndicator_of_mem :
  ∀ {E : Type u} {X : Set E} {x : E}, x ∈ X →
    ConsensusADMM.extendedIndicator X x = 0)
#check (ConsensusADMM.extendedIndicator_of_not_mem :
  ∀ {E : Type u} {X : Set E} {x : E}, x ∉ X →
    ConsensusADMM.extendedIndicator X x = ⊤)

/- Compatibility checks for the migrated polyhedral-set API. -/
#check (ConsensusADMM.IsPolyhedralSet :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E], Set E → Prop)
#check (ConsensusADMM.polyhedralSet_iff :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E},
    ConsensusADMM.IsPolyhedralSet C ↔
      ∃ n : ℕ, ∃ a : Fin n → E, ∃ b : Fin n → ℝ,
        C = {z | ∀ i, inner ℝ (a i) z ≤ b i})
#check (ConsensusADMM.IsCompactConvexPolytope :
  ∀ {E : Type u} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E],
    Set E → Prop)
#check (ConsensusADMM.compactConvexPolytope_iff :
  ∀ {E : Type u} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
      {X : Set E},
    ConsensusADMM.IsCompactConvexPolytope X ↔
      IsCompact X ∧ Convex ℝ X ∧
        ∃ vertices : Finset E, X = convexHull ℝ (vertices : Set E))

/- Compatibility checks for the migrated piecewise-quadratic objective API. -/
#check (ConsensusADMM.IsFiniteClosedConvexPiecewiseQuadratic :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (E → ℝ) → Prop)
#check (ConsensusADMM.finiteClosedConvexPiecewiseQuadratic_iff :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ},
    ConsensusADMM.IsFiniteClosedConvexPiecewiseQuadratic f ↔
      ConvexOn ℝ Set.univ f ∧
        IsClosed {p : E × ℝ | f p.1 ≤ p.2} ∧
        ∃ n : ℕ, ∃ cells : Fin n → Set E,
          ∃ q : Fin n → E →L[ℝ] E, ∃ l : Fin n → E, ∃ c : Fin n → ℝ,
            (∀ z, ∃ i, z ∈ cells i) ∧
            ∀ i, ConsensusADMM.IsPolyhedralSet (cells i) ∧
              ∀ z ∈ cells i,
                f z = inner ℝ (q i z) z / 2 + inner ℝ (l i) z + c i)
