/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open InnerProductSpace (toDualMap)
open Matrix

section

variable {E : Type u} {m : ℕ}

/- Proposition 8.11 is `source-facing` in the Chapter 8 dual projected-subgradient API. Domain
sampling against the existing project owners shows that the canonical subgradient surface is
Chapter 3's `strongDualSubdifferential`; the genuinely new object here is only the dual function
`q`. Since the textbook writes the subgradient as the multiplier-space vector `-g(x_λ)`, the main
statement uses the canonical Riesz bridge `toDualMap` rather than introducing a second local
subgradient owner. -/
recall strongDualSubdifferential

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- The Chapter 8 dual function `q` attached to the inequality-constrained problem data `X`, `f`,
and `g`. On the nonnegative orthant it is the infimum of the Lagrangian
`x ↦ f x + λᵀ g(x)` over `X`; outside the orthant it is set to `⊥` so that `-q` has effective
domain exactly the multiplier region `λ ≥ 0`. -/
def dualFunction (X : Set E) (f : E → ℝ) (g : E → Λ) (lam : Λ) : EReal :=
  if _ : ∀ i : Fin m, 0 ≤ lam i then
    sInf ((fun x : E ↦ ((f x + dotProduct lam (g x) : ℝ) : EReal)) '' X)
  else
    ⊥

-- Proof sketch: unfold `dualFunction`; under coordinatewise nonnegativity of `λ`, the defining
-- `if` reduces to the Lagrangian-infimum branch.
/-- On the nonnegative orthant, `dualFunction X f g λ` is exactly the infimum over `X` of the
Lagrangian values `f x + λᵀ g(x)`. -/
theorem dualFunction_eq_sInf_of_nonneg
    (X : Set E) (f : E → ℝ) (g : E → Λ) (lam : Λ)
    (hlam : ∀ i : Fin m, 0 ≤ lam i) :
    dualFunction X f g lam =
      sInf ((fun x : E ↦ ((f x + dotProduct lam (g x) : ℝ) : EReal)) '' X) := by
  -- Unfold the Chapter 8 dual function and take the nonnegative branch of the defining `if`.
  simp [dualFunction, hlam]

-- Proof sketch: unfold `dualFunction`; if `λ` is not coordinatewise nonnegative, the defining
-- `if` reduces to the outside-the-orthant branch.
/-- Outside the nonnegative orthant, the Chapter 8 dual function is `⊥`. -/
@[simp] theorem dualFunction_eq_bot_of_not_nonneg
    (X : Set E) (f : E → ℝ) (g : E → Λ) (lam : Λ)
    (hlam : ¬ ∀ i : Fin m, 0 ≤ lam i) :
    dualFunction X f g lam = ⊥ := by
  -- Unfold the dual function and select the outside-the-orthant branch.
  simp [dualFunction, hlam]

/-- Helper for Proposition 8.11: every multiplier in the effective domain of `-q` is
coordinatewise nonnegative, since outside the orthant the dual function is `⊥`. -/
lemma mem_effective_domain_neg_dualFunction_imp_nonneg
    (X : Set E) (f : E → ℝ) (g : E → Λ) (mu : Λ)
    (hmu : mu ∈ effective_domain (fun ν ↦ -dualFunction X f g ν)) :
    ∀ i : Fin m, 0 ≤ mu i := by
  intro i
  by_contra hi
  have hnot : ¬ ∀ j : Fin m, 0 ≤ mu j := by
    intro hnonneg
    exact hi (hnonneg i)
  have hdual_bot : dualFunction X f g mu = ⊥ :=
    dualFunction_eq_bot_of_not_nonneg X f g mu hnot
  -- If `q(μ) = ⊥`, then `-q(μ) = ⊤`, so `μ` cannot lie in the effective domain of `-q`.
  have hnot_mem : mu ∉ effective_domain (fun ν ↦ -dualFunction X f g ν) := by
    simp [effective_domain, hdual_bot]
  exact hnot_mem hmu

/-- Helper for Proposition 8.11: on the nonnegative orthant, any feasible primal point gives an
upper bound on the dual infimum. -/
lemma dualFunction_le_lagrangian_value_of_nonneg
    (X : Set E) (f : E → ℝ) (g : E → Λ) (mu : Λ) {x : E}
    (hx : x ∈ X) (hmu : ∀ i : Fin m, 0 ≤ mu i) :
    dualFunction X f g mu ≤ ((f x + dotProduct mu (g x) : ℝ) : EReal) := by
  -- Rewrite `q(μ)` as the infimum of Lagrangian values and use `x` as a witness in the image.
  rw [dualFunction_eq_sInf_of_nonneg X f g mu hmu]
  exact sInf_le ⟨x, hx, rfl⟩

/-- Helper for Proposition 8.11: the Euclidean Riesz-map pairing is the coordinate dot product on
the multiplier space. -/
private lemma toDualMap_apply_eq_dotProduct
    (u v : Λ) :
    ((toDualMap ℝ Λ v) u : ℝ) = dotProduct u v := by
  -- Convert the inner-product pairing on Euclidean space to the explicit coordinate formula.
  simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp v.ofLp u.ofLp)

-- Proof sketch: for any multiplier `μ`, use the feasible point `xLambda` in the infimum defining
-- `dualFunction X f g μ` to obtain
-- `q(μ) ≤ f(xLambda) + μᵀ g(xLambda) = q(λ) + (μ - λ)ᵀ g(xLambda)`. After negating, this is
-- exactly the subgradient inequality for `-q` at `λ`, and `toDualMap` identifies the vector
-- `-(g xLambda)` with the corresponding continuous linear functional on the multiplier space.
/-- Proposition 8.11: if the infimum defining the dual function `q(λ)` is attained at
`x_λ ∈ X`, then the multiplier-space vector `-g(x_λ)` represents a strong-dual subgradient of
`-q` at `λ`. -/
theorem neg_constraint_vector_mem_strongDualSubdifferential_neg_dualFunction_of_attained
    (X : Set E) (f : E → ℝ) (g : E → Λ) (lam : Λ) (xLambda : E)
    (hxLambda : xLambda ∈ X)
    (hattained :
      dualFunction X f g lam =
        ((f xLambda + dotProduct lam (g xLambda) : ℝ) : EReal)) :
    toDualMap ℝ Λ (-(g xLambda)) ∈
      strongDualSubdifferential (fun μ ↦ -dualFunction X f g μ) lam := by
  -- Rewrite strong-dual subgradient membership to the Chapter 3 subgradient inequality on the
  -- effective domain of `-q`.
  rw [mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨?_, ?_⟩
  · -- The attained value at `λ` is finite, so `λ` belongs to the effective domain of `-q`.
    rw [effective_domain]
    refine
      (lt_top_iff_ne_top :
        -dualFunction X f g lam < (⊤ : EReal) ↔ -dualFunction X f g lam ≠ (⊤ : EReal)).2 ?_
    intro htop
    have hdual_bot : dualFunction X f g lam = ⊥ := by
      simpa using htop
    exact EReal.coe_ne_bot _ (hattained.symm.trans hdual_bot)
  · intro mu hmu
    -- Effective-domain multipliers cannot lie outside the nonnegative orthant.
    have hMuNonneg : ∀ i : Fin m, 0 ≤ mu i :=
      mem_effective_domain_neg_dualFunction_imp_nonneg X f g mu hmu
    -- Use the attained primal point `xLambda` as the fixed witness in the infimum defining `q(μ)`.
    have hdual_le :
        dualFunction X f g mu ≤ ((f xLambda + dotProduct mu (g xLambda) : ℝ) : EReal) :=
      dualFunction_le_lagrangian_value_of_nonneg X f g mu hxLambda hMuNonneg
    -- Identify the Riesz pairing with the negative constraint vector.
    have hpair :
        ((toDualMap ℝ Λ (-(g xLambda)) : Module.Dual ℝ Λ) (mu - lam) : ℝ) =
          -dotProduct (mu - lam) (g xLambda) := by
      have hbase :
          ((toDualMap ℝ Λ (g xLambda) : Module.Dual ℝ Λ) (mu - lam) : ℝ) =
            dotProduct (mu - lam) (g xLambda) :=
        toDualMap_apply_eq_dotProduct (mu - lam) (g xLambda)
      simpa [InnerProductSpace.toDualMap_apply_apply] using congrArg (fun z : ℝ ↦ -z) hbase
    -- Negating the witness bound is the source proof's subgradient inequality for `-q`.
    have hneg :
        -((f xLambda + dotProduct mu (g xLambda) : ℝ) : EReal) ≤
          -dualFunction X f g mu := by
      exact (EReal.neg_le_neg_iff).2 hdual_le
    calc
      -dualFunction X f g mu
          ≥ -((f xLambda + dotProduct mu (g xLambda) : ℝ) : EReal) := hneg
      _ = -dualFunction X f g lam +
            (((toDualMap ℝ Λ (-(g xLambda)) : Module.Dual ℝ Λ) (mu - lam) : ℝ) : EReal) := by
          rw [hattained, hpair]
          have hsub :
              dotProduct (mu - lam) (g xLambda) =
                dotProduct mu (g xLambda) - dotProduct lam (g xLambda) := by
            exact sub_dotProduct mu lam (g xLambda)
          have hreal :
              -(f xLambda + dotProduct mu (g xLambda)) =
                -(f xLambda + dotProduct lam (g xLambda)) +
                  (-dotProduct (mu - lam) (g xLambda)) := by
            linarith
          calc
            -((f xLambda + dotProduct mu (g xLambda) : ℝ) : EReal)
                = (((-(f xLambda + dotProduct mu (g xLambda)) : ℝ)) : EReal) := by
                    rw [EReal.coe_add,
                      EReal.neg_add
                        (Or.inl (EReal.coe_ne_bot _))
                        (Or.inl (EReal.coe_ne_top _))]
                    simp [sub_eq_add_neg, EReal.coe_add, add_comm]
            _ = (((-(f xLambda + dotProduct lam (g xLambda)) +
                    -dotProduct (mu - lam) (g xLambda) : ℝ)) : EReal) := by
                  exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
            _ = -((f xLambda + dotProduct lam (g xLambda) : ℝ) : EReal) +
                  (((-dotProduct (mu - lam) (g xLambda) : ℝ)) : EReal) := by
                    rw [EReal.coe_add, EReal.coe_add,
                      EReal.neg_add
                        (Or.inl (EReal.coe_ne_bot _))
                        (Or.inl (EReal.coe_ne_top _))]
                    simp [sub_eq_add_neg, add_comm, add_assoc]

end
