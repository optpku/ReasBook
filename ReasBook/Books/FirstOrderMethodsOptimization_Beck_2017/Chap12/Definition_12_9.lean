/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {ι : Sort*}
variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 12.9 is a `bridge/view` recall: the orthogonal projection onto an intersection of
closed convex sets is not a new owner abstraction, but the Chapter 3 owner `projectionPoint`
applied to the total intersection.

Domain sampling identifies the canonical owner abstraction and the relevant derived API:
- `projectionPoint` from Proposition 3.12 is the chapter owner of orthogonal projection onto a
  nonempty closed convex set;
- `isClosed_iInter` and `convex_iInter` from mathlib provide the closedness and convexity of the
  total intersection from the family hypotheses;
- `IsMinOn` is the canonical minimizer predicate for the projection problem.

Primitive owner data are only the set `S` together with its nonemptiness, closedness, and
convexity. For an intersection `S = ⋂ i, C i`, the familywise assumptions are auxiliary bridge data
used only to derive `IsClosed S` and `Convex ℝ S`, so the public recall surface stays at the owner
level rather than rebuilding intersection-specific wrappers. -/
section

variable (C : ι → Set E) (hC_nonempty : (⋂ i, C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i)) (hC_convex : ∀ i, Convex ℝ (C i))

local notation "S" => ⋂ i, C i
local notation "hS_closed" => isClosed_iInter hC_closed
local notation "hS_convex" => convex_iInter hC_convex
local notation "P" =>
  projectionPoint S hC_nonempty hS_closed hS_convex

/- Definition 12.9: for `S = ⋂ i, C i`, once the total intersection is known to be nonempty,
closed, and convex, its orthogonal projection is the canonical point projection `projectionPoint`
onto `S`, equivalently the optimal solution of `min_x {(1 / 2) ‖x - d‖^2 : x ∈ S}`. -/
#check (P : E → E)

/- The owner membership theorem applies directly to the total feasible set `S`. -/
#check (projectionPoint_mem S hC_nonempty hS_closed hS_convex :
  ∀ d : E, P d ∈ S)

/- The owner minimizer theorem applies directly to the half squared-distance problem on `S`. -/
#check (projectionPoint_isMinOn S hC_nonempty hS_closed hS_convex :
  ∀ d : E, IsMinOn (fun x ↦ ‖x - d‖ ^ (2 : ℕ) / 2) S (P d))

/- The owner uniqueness theorem applies directly to characterize any feasible minimizer on `S` as
the projection point. -/
#check
    (eq_projectionPoint_of_mem_isMinOn
      S hC_nonempty hS_closed hS_convex :
  ∀ (d : E) {x : E}, x ∈ S →
    IsMinOn (fun y ↦ ‖y - d‖ ^ (2 : ℕ) / 2) S x →
      x = P d)

end

end
