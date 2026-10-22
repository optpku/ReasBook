/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_3.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_11.StrictComplementarity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_21.Face
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Order.Filter.Extr

public section

namespace ActiveSet

universe u

variable {ι : Type u}

/-
Remark 9.21.

The source remark has three clauses. Clause `(1)` records finite identification
of the optimal active set under the surrounding convergence and strict
complementarity hypotheses. Clause `(2)` introduces the optimal face `(9.33)`.
Clause `(3)` passes to the reduced Newton subproblem `(9.32)` on that face,
uses eventual interiority in the optimal face, and concludes quadratic
convergence.

The current repository snapshot already exposes the Chapter 9 owners
`NonnegativeOrthant.StrictComplementarity`, `ActiveSet.active`,
`ActiveSet.face`, and the reduced-stage GPRN API from Algorithm 9.3.3,
including `GPRN.IsReducedDirectionSequence` and
`GPRN.IsExactReducedLineSearch`. The source local-minimizer clause for problem
`(9.16)` already matches
`IsLocalMinOn J (NonnegativeOrthant.feasibleSet n) fStar`, and eventual
interiority on the optimal face already matches ordinary set interior. Only the
final quadratic-convergence conclusion still lacks a dedicated Chapter 9 owner,
so only that remaining semantic component stays as an explicit local binder
below.
-/

/- Remark 9.21 (1).

Under the source convergence and strict-complementarity hypotheses, the active
sets of the iterates eventually agree with the optimal active set. This clause
now reuses the repository owners
`IsLocalMinOn J (NonnegativeOrthant.feasibleSet n) fStar` for the local
minimizer in `(9.16)`, `NonnegativeOrthant.StrictComplementarity` for `(9.20)`,
and `ActiveSet.active` for the coordinate active set.
-/
#check
  ∀ (n : ℕ) (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (iterates : ℕ → EuclideanSpace ℝ (Fin n)) (fStar : EuclideanSpace ℝ (Fin n)),
      Filter.Tendsto iterates Filter.atTop (nhds fStar) →
        IsLocalMinOn J (NonnegativeOrthant.feasibleSet n) fStar →
          NonnegativeOrthant.StrictComplementarity J fStar →
            ∃ v0 : ℕ,
              ∀ v ≥ v0,
                active (fun i x ↦ x i) (iterates v) =
                  active (fun i x ↦ x i) fStar

/- Remark 9.21 (2). The optimal face `(9.33)` attached to an active set is the
canonical owner `ActiveSet.face`. -/
#check ActiveSet.face

/-- If the active sets of the iterates agree with the optimal active set from
some index `v0` onward, then the associated faces also agree from `v0`
onward. This is the reusable fixed-cutoff bridge behind the source's
"eventually" formulation. -/
theorem face_eq_of_activeSet_eq_eventually
    {H : Type _} (C : Set H) (c : ι → H → ℝ) (iterates : ℕ → H) (fStar : H)
    (v0 v : ℕ) (hactive : ∀ w ≥ v0, active c (iterates w) = active c fStar)
    (hv : v0 ≤ v) :
    face C c (iterates v) = face C c fStar :=
  face_eq_of_activeSet_eq C c (hactive v hv)

/-- This is the reusable face-equality bridge used by source clause `(3)`.
If the active sets of the iterates eventually agree with the optimal active
set, then the associated faces eventually agree with the optimal face. -/
theorem eventually_eq_face_of_eventually_eq_activeSet
    {H : Type _} (C : Set H) (c : ι → H → ℝ) (iterates : ℕ → H) (fStar : H)
    (hactive : ∃ v0 : ℕ, ∀ v ≥ v0, active c (iterates v) = active c fStar) :
    ∃ v0 : ℕ, ∀ v ≥ v0, face C c (iterates v) = face C c fStar := by
  rcases hactive with ⟨v0, hv0⟩
  refine ⟨v0, ?_⟩
  intro v hv
  exact face_eq_of_activeSet_eq_eventually C c iterates fStar v0 v hv0 hv

/-
Remark 9.21 (3).

Once the optimal face is identified, the source continues by passing to the
reduced Newton subproblem `(9.32)` on that face, observing eventual interiority
inside the optimal face, and concluding quadratic convergence from the Newton
analysis. This clause now reuses the reduced-stage GPRN owners
`GPRN.projectedStages`, `GPRN.iterates`, `GPRN.IsReducedDirectionSequence`, and
`GPRN.IsExactReducedLineSearch`, together with ordinary set-interior language
on the identified optimal face. Only the quadratic-convergence predicate
remains explicit until the corresponding Chapter 9 owner is formalized.
-/
section

variable [Fintype ι] [DecidableEq ι]

#check
  ∀ (C : Set (EuclideanSpace ℝ ι))
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ)
    (reducedDirections : ℕ → EuclideanSpace ℝ ι)
    (f0 fStar : EuclideanSpace ℝ ι)
    (convergesQuadraticallyTo :
      (ℕ → EuclideanSpace ℝ ι) → EuclideanSpace ℝ ι → Prop),
      (∃ v0 : ℕ,
        ∀ v ≥ v0,
          active (fun i f ↦ f i) (GPRN.projectedStages P J σ τ f0 reducedDirections v) =
            active (fun i f ↦ f i) fStar) →
        GPRN.IsReducedDirectionSequence P J hessianMatrix σ τ f0 reducedDirections →
        GPRN.IsExactReducedLineSearch P J σ τ f0 reducedDirections →
          ∃ v0 : ℕ,
            (∀ v ≥ v0,
              GPRN.projectedStages P J σ τ f0 reducedDirections v ∈
                interior (face C (fun i f ↦ f i) fStar)) ∧
              convergesQuadraticallyTo
                (fun k ↦ GPRN.iterates P J σ τ f0 reducedDirections (v0 + k))
                fStar

end

end ActiveSet
