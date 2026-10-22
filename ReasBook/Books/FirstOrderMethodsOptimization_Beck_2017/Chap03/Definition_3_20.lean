/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_5_feasible_set

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} {m : ℕ}

/-
Definition 3.20 is `source-facing`. The ambient domain is finite-family inequality-constrained
optimization, and the owner abstractions for later KKT/Fritz-John developments are the chapter
feasible-set owner `inequality_feasible_set` together with the strict feasible set cut out by the
same constraint family. The primitive data are only the constraint family `g`; Slater's condition
is derived from the strict feasible-set owner as its nonemptiness. -/

/-- The strict feasible set of the inequality-constrained problem cut out by the family `g`. -/
def strict_inequality_feasible_set (g : Fin m → E → ℝ) : Set E :=
  {x | ∀ i, g i x < 0}

variable {g : Fin m → E → ℝ}

/-- Membership in `strict_inequality_feasible_set g` means satisfying every inequality
constraint strictly. -/
@[simp] theorem mem_strict_inequality_feasible_set {x : E} :
    x ∈ strict_inequality_feasible_set g ↔ ∀ i, g i x < 0 :=
  Iff.rfl

/-- Every strict feasible point is feasible for the inequality-constrained problem. -/
theorem strict_inequality_feasible_set_subset_inequality_feasible_set :
    strict_inequality_feasible_set g ⊆ inequality_feasible_set g := fun _ hx i ↦
  le_of_lt (hx i)

/-- Definition 3.20: Slater's condition for the inequality-constrained problem with constraint
family `g` means that there exists a point strictly satisfying every inequality `g_i(x) < 0`. -/
def slaters_condition (g : Fin m → E → ℝ) : Prop :=
  (strict_inequality_feasible_set g).Nonempty

/-- Slater's condition holds exactly when some point satisfies every inequality constraint
strictly. -/
@[simp] theorem slaters_condition_iff (g : Fin m → E → ℝ) :
    slaters_condition g ↔ ∃ x : E, ∀ i : Fin m, g i x < 0 :=
  Iff.rfl

end
