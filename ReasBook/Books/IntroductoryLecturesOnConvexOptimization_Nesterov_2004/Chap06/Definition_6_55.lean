/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/- Definition 6.55 lies in the chapter's `WithTop`-valued convex-analysis domain.

Primary domain:
- restricted duality for `ℝ ∪ {+∞}`-valued functions on a real topological module, organized
  around the effective domain and finite real part of the primal function.

Sampled owner-style declarations:
- `withTopEffectiveDomain` and the notation `dom f` in `Chap03/Definition_3_3`, the chapter owner
  for the finite-value domain of a `WithTop ℝ`-valued function;
- `withTopRealPart` in `Chap03/Definition_3_3`, the chapter owner for the finite real
  representative extended by `0` off the effective domain;
- `withTopRealPart_eq_untop` in `Chap03/Definition_3_3`, the atomic bridge identifying
  `withTopRealPart F x` with the finite value `F x` on `dom F`;
- `mem_withTopEffectiveDomain_iff` in `Chap03/Definition_3_3`, the atomic membership bridge for
  the same owner surface.

Best owner abstraction:
- core/canonical: `dom F` and `withTopRealPart F`;
- source-facing: the restricted dual maximand and restricted dual function below.

Primitive data:
- the feasible set `Q : Set E`;
- the extended-real-valued function `F : E → WithTop ℝ`;
- the feasible base point `xBar : Q ∩ dom F` for the restricted-dual owner;
- the finite-domain base point `xBar : dom F` for the maximand.

Derived API:
- the restricted dual maximand `s (xBar - x) + F(xBar) - F(x)` on finite points of `F`, read
  through `withTopRealPart F`;
- the restricted dual function as the `sSup` over the nonempty finite feasible set
  `Q ∩ dom F`, witnessed by the chosen base point `xBar`;
- the direct evaluation theorem expanding that supremum.

Source/core/bridge triage:
- source-facing: `restrictedDualMaximand` and `restrictedDualFunction`;
- core/canonical: `dom F` and `withTopRealPart F`;
- bridge/view: the evaluation theorem `restrictedDualFunction_apply`.

This file reuses the Chapter 3 owner abstraction directly and keeps only the genuinely new
restricted-dual constructions as public declarations. Since the textbook formula reads
`F(xBar) - F(x)`, the source-facing surface below keeps `xBar` and `x` on the finite-value domain
instead of totalizing those terms by the off-domain convention built into `withTopRealPart`. The
restricted-dual owner itself keeps the feasible base-point hypothesis `xBar ∈ Q ∩ dom F`, which
is exactly the data needed to avoid an empty `WithTop ℝ` supremum.
-/

/-- The affine gap maximand used in the restricted dual function, evaluated at finite points of
`F`. -/
def restrictedDualMaximand
    (F : E → WithTop ℝ) (xBar : dom F) (s : StrongDual ℝ E) (x : dom F) : ℝ :=
  s ((xBar : E) - x) + withTopRealPart F xBar - withTopRealPart F x

/-- Definition 6.55: the restricted dual function of an `ℝ ∪ {+∞}`-valued function `F` with
respect to `(xBar, Q)` with `xBar ∈ Q ∩ dom F` is the supremum over the finite feasible points
`x ∈ Q ∩ dom F` of the affine gap `s (xBar - x) + F(xBar) - F(x)`. The feasible-base-point
hypothesis keeps the index set nonempty, so this `WithTop ℝ` supremum is mathematically faithful.
In the textbook setting where `Q` is bounded closed convex and the maximum is attained, this
supremum is the displayed maximum. -/
def restrictedDualFunction
    (Q : Set E) (F : E → WithTop ℝ) (xBar : ↥(Q ∩ dom F)) : StrongDual ℝ E → WithTop ℝ :=
  fun s ↦
    sSup <| Set.range fun x : ↥(Q ∩ dom F) ↦
      ((restrictedDualMaximand F ⟨xBar, xBar.2.2⟩ s ⟨x, x.2.2⟩ : ℝ) : WithTop ℝ)

/-- Evaluating the restricted dual function recovers the defining supremum over the finite feasible
points `x ∈ Q ∩ dom F`. -/
theorem restrictedDualFunction_apply
    (Q : Set E) (F : E → WithTop ℝ) (xBar : ↥(Q ∩ dom F)) (s : StrongDual ℝ E) :
    restrictedDualFunction Q F xBar s =
      sSup (Set.range fun x : ↥(Q ∩ dom F) ↦
        ((restrictedDualMaximand F ⟨xBar, xBar.2.2⟩ s ⟨x, x.2.2⟩ : ℝ) : WithTop ℝ)) :=
  rfl

end
