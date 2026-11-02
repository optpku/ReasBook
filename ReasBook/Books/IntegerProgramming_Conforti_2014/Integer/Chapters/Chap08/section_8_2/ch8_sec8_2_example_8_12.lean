import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- This file keeps the source-facing one-tree family formulation and packages the generic `0,1`
-- edge-set incidence vector as the reusable owner for the convex-hull side of Example 8.12.

section Example812

variable {V E : Type}

/-- The cost `c(T)` of an edge set `T`, obtained by summing the edge costs over the chosen edges.
-/
def one_tree_cost (c : E → ℝ) (T : Finset E) : ℝ :=
  T.sum c

/-- `one_tree_cost c T` is the sum of the edge costs over `T`. -/
theorem one_tree_cost_eq_sum
    (c : E → ℝ) (T : Finset E) :
    one_tree_cost c T = T.sum c :=
  rfl

/-- The objective value `sum_T c(T) lambda_T` of the Held-Karp Dantzig-Wolfe relaxation. -/
def held_karp_dantzig_wolfe_objective
    (c : E → ℝ)
    (oneTrees : Finset (Finset E))
    (lam : Finset E → ℝ) : ℝ :=
  oneTrees.sum fun T ↦ one_tree_cost c T * lam T

/-- `held_karp_dantzig_wolfe_objective c oneTrees lam` is the sum of the 1-tree costs weighted by
the multipliers `lam`. -/
theorem held_karp_dantzig_wolfe_objective_eq
    (c : E → ℝ)
    (oneTrees : Finset (Finset E))
    (lam : Finset E → ℝ) :
    held_karp_dantzig_wolfe_objective c oneTrees lam =
      oneTrees.sum (fun T ↦ one_tree_cost c T * lam T) :=
  rfl

variable [DecidableEq E]

/-- The `0,1` incidence vector of an edge set `T`. -/
def one_tree_incidence_vector (T : Finset E) : E → ℝ :=
  fun e ↦ if e ∈ T then 1 else 0

/-- `one_tree_incidence_vector T` has value `1` on the edges of `T` and `0` off `T`. -/
@[simp] theorem one_tree_incidence_vector_apply
    (T : Finset E) (e : E) :
    one_tree_incidence_vector T e = if e ∈ T then 1 else 0 :=
  rfl

/-- The incidence vectors of the listed 1-trees. -/
def one_tree_incidence_vectors
    (oneTrees : Finset (Finset E)) : Set (E → ℝ) :=
  (↑oneTrees : Set (Finset E)).image one_tree_incidence_vector

/-- A vector belongs to `one_tree_incidence_vectors oneTrees` exactly when it is the incidence
vector of one of the listed 1-trees. -/
theorem mem_one_tree_incidence_vectors_iff
    (oneTrees : Finset (Finset E))
    {x : E → ℝ} :
    x ∈ one_tree_incidence_vectors oneTrees ↔
      ∃ T ∈ oneTrees, x = one_tree_incidence_vector T := by
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, rfl⟩

/-- The convex-hull feasible region from Example 8.12: degree `2` away from the distinguished
root and membership in the convex hull of the incidence vectors of the 1-tree family. -/
def held_karp_one_tree_bound_feasible_set
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E)) : Set (E → ℝ) :=
  {x : E → ℝ |
    (∀ i, i ≠ root → (delta i).sum x = 2) ∧
      x ∈ convexHull ℝ (one_tree_incidence_vectors oneTrees)}

/-- Membership in `held_karp_one_tree_bound_feasible_set root delta oneTrees` means satisfying the
degree equations away from `root` and belonging to the convex hull of the listed 1-tree incidence
vectors. -/
theorem mem_held_karp_one_tree_bound_feasible_set_iff
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (x : E → ℝ) :
    x ∈ held_karp_one_tree_bound_feasible_set root delta oneTrees ↔
      (∀ i, i ≠ root → (delta i).sum x = 2) ∧
        x ∈ convexHull ℝ (one_tree_incidence_vectors oneTrees) :=
  Iff.rfl

/-- The value of the convex-hull one-tree bound from Example 8.12. -/
noncomputable def held_karp_one_tree_bound_value
    [Fintype E]
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (c : E → ℝ) : ℝ :=
  sInf
    ((fun x : E → ℝ ↦ ∑ e, c e * x e) ''
      held_karp_one_tree_bound_feasible_set root delta oneTrees)

/-- The feasible set of the Held-Karp Dantzig-Wolfe master problem over the 1-tree family. -/
def held_karp_dantzig_wolfe_feasible_set
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E)) : Set (Finset E → ℝ) :=
  {lam : Finset E → ℝ |
    (∀ i, i ≠ root →
      oneTrees.sum (fun T ↦ ((delta i ∩ T).card : ℝ) * lam T) = 2) ∧
      (oneTrees.sum lam = 1) ∧
      ∀ T ∈ oneTrees, 0 ≤ lam T}

/-- Membership in `held_karp_dantzig_wolfe_feasible_set root delta oneTrees` means satisfying the
degree equations away from `root`, the convexity equation, and nonnegativity on the listed
1-trees. -/
theorem mem_held_karp_dantzig_wolfe_feasible_set_iff
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (lam : Finset E → ℝ) :
    lam ∈ held_karp_dantzig_wolfe_feasible_set root delta oneTrees ↔
      (∀ i, i ≠ root →
        oneTrees.sum (fun T ↦ ((delta i ∩ T).card : ℝ) * lam T) = 2) ∧
        (oneTrees.sum lam = 1) ∧
        ∀ T ∈ oneTrees, 0 ≤ lam T :=
  Iff.rfl

/-- The value of the Held-Karp Dantzig-Wolfe relaxation over the family of 1-trees. -/
noncomputable def held_karp_dantzig_wolfe_relaxation_value
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (c : E → ℝ) : ℝ :=
  sInf
    (held_karp_dantzig_wolfe_objective c oneTrees ''
      held_karp_dantzig_wolfe_feasible_set root delta oneTrees)

/-- Helper for Example 8.12: summing the `0,1` incidence vector of `T` over a finite edge set `s`
counts the edges lying in `s ∩ T`. -/
lemma sum_incidence_eq_card_inter
    (s T : Finset E) :
    s.sum (one_tree_incidence_vector T) = ((s ∩ T).card : ℝ) := by
  -- The incidence vector contributes `1` exactly on the edges in the intersection.
  simp [one_tree_incidence_vector]

/-- Helper for Example 8.12: the edge-cost dot product with the incidence vector of `T` is the
stored one-tree cost `c(T)`. -/
lemma cost_dot_incidence_eq_one_tree_cost
    [Fintype E]
    (c : E → ℝ) (T : Finset E) :
    (∑ e, c e * one_tree_incidence_vector T e) = one_tree_cost c T := by
  -- The zero entries off `T` disappear, leaving the sum of edge costs over `T`.
  simp [one_tree_cost, one_tree_incidence_vector, mul_ite, mul_one, mul_zero]

/-- Helper for Example 8.12: every feasible Dantzig-Wolfe coefficient vector induces a feasible
convex-combination point with the same objective value. -/
lemma exists_one_tree_bound_point_of_master_feasible
    [Fintype E]
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (c : E → ℝ)
    (lam : Finset E → ℝ)
    (hLam : lam ∈ held_karp_dantzig_wolfe_feasible_set root delta oneTrees) :
    ∃ x, x ∈ held_karp_one_tree_bound_feasible_set root delta oneTrees ∧
      held_karp_dantzig_wolfe_objective c oneTrees lam = ∑ e, c e * x e := by
  rcases hLam with ⟨hDegree, hSum, hNonneg⟩
  let x : E → ℝ := fun e ↦ oneTrees.sum fun T ↦ lam T * one_tree_incidence_vector T e
  have hxDegree : ∀ i, i ≠ root → (delta i).sum x = 2 := by
    intro i hi
    -- Swap the edge/tree sums and rewrite the inner incidence sum as a cardinality.
    calc
      (delta i).sum x =
          (delta i).sum (fun e ↦ oneTrees.sum fun T ↦ lam T * one_tree_incidence_vector T e) := by
        rfl
      _ = oneTrees.sum (fun T ↦ (delta i).sum fun e ↦ lam T * one_tree_incidence_vector T e) := by
        rw [Finset.sum_comm]
      _ = oneTrees.sum (fun T ↦ ((delta i ∩ T).card : ℝ) * lam T) := by
        refine Finset.sum_congr rfl ?_
        intro T hT
        calc
          (delta i).sum (fun e ↦ lam T * one_tree_incidence_vector T e) =
              lam T * ((delta i).sum fun e ↦ one_tree_incidence_vector T e) := by
            rw [← Finset.mul_sum]
          _ = lam T * ((delta i ∩ T).card : ℝ) := by
            rw [sum_incidence_eq_card_inter]
          _ = ((delta i ∩ T).card : ℝ) * lam T := by
            rw [mul_comm]
      _ = 2 := hDegree i hi
  have hxHull : x ∈ convexHull ℝ (one_tree_incidence_vectors oneTrees) := by
    let w : {T // T ∈ oneTrees} → ℝ := fun T ↦ lam T.1
    let z : {T // T ∈ oneTrees} → E → ℝ := fun T ↦ one_tree_incidence_vector T.1
    have hwNonneg : ∀ T, 0 ≤ w T := by
      intro T
      exact hNonneg T.1 T.2
    have hwSum : ∑ T, w T = 1 := by
      rw [Finset.univ_eq_attach, Finset.sum_attach]
      simpa [w] using hSum
    have hzMem : ∀ T, z T ∈ one_tree_incidence_vectors oneTrees := by
      intro T
      exact (mem_one_tree_incidence_vectors_iff oneTrees).2 ⟨T.1, T.2, rfl⟩
    have hxEq : ∑ T, w T • z T = x := by
      -- The barycentric combination is exactly the mixed incidence vector `x`.
      ext e
      simpa [x, w, z, Pi.smul_apply, mul_assoc] using
        (oneTrees.sum_attach (f := fun T ↦ if e ∈ T then lam T else 0))
    exact mem_convexHull_of_exists_fintype w z hwNonneg hwSum hzMem hxEq
  have hObjective :
      held_karp_dantzig_wolfe_objective c oneTrees lam = ∑ e, c e * x e := by
    -- Swap the edge/tree sums and collapse each single-tree contribution to `c(T)`.
    calc
      held_karp_dantzig_wolfe_objective c oneTrees lam =
          oneTrees.sum (fun T ↦ one_tree_cost c T * lam T) := by
        rfl
      _ = oneTrees.sum (fun T ↦ ∑ e, c e * (lam T * one_tree_incidence_vector T e)) := by
        refine Finset.sum_congr rfl ?_
        intro T hT
        calc
          one_tree_cost c T * lam T = (∑ e, c e * one_tree_incidence_vector T e) * lam T := by
            rw [cost_dot_incidence_eq_one_tree_cost]
          _ = ∑ e, (c e * one_tree_incidence_vector T e) * lam T := by
            rw [Finset.sum_mul]
          _ = ∑ e, c e * (lam T * one_tree_incidence_vector T e) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            ring_nf
      _ = ∑ e, oneTrees.sum (fun T ↦ c e * (lam T * one_tree_incidence_vector T e)) := by
        rw [Finset.sum_comm]
      _ = ∑ e, c e * x e := by
        refine Finset.sum_congr rfl ?_
        intro e he
        rw [← Finset.mul_sum]
  exact ⟨x, ⟨hxDegree, hxHull⟩, hObjective⟩

/-- Helper for Example 8.12: every feasible convex-hull point admits feasible Dantzig-Wolfe
coefficients with the same objective value. -/
lemma exists_master_feasible_of_one_tree_bound_point
    [Fintype E]
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (c : E → ℝ)
    (x : E → ℝ)
    (hx : x ∈ held_karp_one_tree_bound_feasible_set root delta oneTrees) :
    ∃ lam, lam ∈ held_karp_dantzig_wolfe_feasible_set root delta oneTrees ∧
      (∑ e, c e * x e) = held_karp_dantzig_wolfe_objective c oneTrees lam := by
  classical
  rcases hx with ⟨hxDegree, hxHull⟩
  rcases (mem_convexHull_iff_exists_fintype).1 hxHull with
    ⟨ι, _, w, z, hwNonneg, hwSum, hzMem, hzEq⟩
  choose tree hTreeMem hTreeEq using
    fun i ↦ (mem_one_tree_incidence_vectors_iff oneTrees).1 (hzMem i)
  let lam : Finset E → ℝ := fun T ↦ ∑ i, if T = tree i then w i else 0
  have hLamNonneg : ∀ T ∈ oneTrees, 0 ≤ lam T := by
    intro T hT
    -- Each aggregated coefficient is a sum of nonnegative witness weights.
    exact Finset.sum_nonneg fun i hi ↦ by
      by_cases hEq : T = tree i
      · simp [hEq, hwNonneg i]
      · simp [hEq]
  have hLamSum : oneTrees.sum lam = 1 := by
    -- Summing the fiber-aggregated coefficients recovers the original convex weights.
    calc
      oneTrees.sum lam = oneTrees.sum (fun T ↦ ∑ i, if T = tree i then w i else 0) := by
        rfl
      _ = ∑ i, oneTrees.sum (fun T ↦ if T = tree i then w i else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ i, w i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [hTreeMem i]
      _ = 1 := hwSum
  have hReconstruct :
      ∀ e, oneTrees.sum (fun T ↦ lam T * one_tree_incidence_vector T e) = x e := by
    intro e
    -- Re-group the convex-hull witness by the represented one-tree.
    calc
      oneTrees.sum (fun T ↦ lam T * one_tree_incidence_vector T e) =
          oneTrees.sum
            (fun T ↦ (∑ i, if T = tree i then w i else 0) * one_tree_incidence_vector T e) := by
        rfl
      _ = oneTrees.sum
            (fun T ↦ ∑ i, (if T = tree i then w i else 0) * one_tree_incidence_vector T e) := by
        refine Finset.sum_congr rfl ?_
        intro T hT
        rw [Finset.sum_mul]
      _ = ∑ i, oneTrees.sum
            (fun T ↦ (if T = tree i then w i else 0) * one_tree_incidence_vector T e) := by
        rw [Finset.sum_comm]
      _ = ∑ i, w i * one_tree_incidence_vector (tree i) e := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          oneTrees.sum (fun T ↦ (if T = tree i then w i else 0) * one_tree_incidence_vector T e) =
              oneTrees.sum
                (fun T ↦ if T = tree i then w i * one_tree_incidence_vector (tree i) e else 0) := by
            refine Finset.sum_congr rfl ?_
            intro T hT
            by_cases hEq : T = tree i
            · simp [hEq]
            · simp [hEq]
          _ = w i * one_tree_incidence_vector (tree i) e := by
            simp [hTreeMem i]
      _ = ∑ i, w i * z i e := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hTreeEq i]
      _ = x e := by
        have hzEq' : (∑ i, w i • z i) e = x e := congrFun hzEq e
        simpa [Pi.smul_apply] using hzEq'
  have hLamDegree :
      ∀ i, i ≠ root →
        oneTrees.sum (fun T ↦ ((delta i ∩ T).card : ℝ) * lam T) = 2 := by
    intro i hi
    -- Convert the aggregated coefficients back to the reconstructed point `x`.
    calc
      oneTrees.sum (fun T ↦ ((delta i ∩ T).card : ℝ) * lam T) =
          oneTrees.sum (fun T ↦ (delta i).sum fun e ↦ lam T * one_tree_incidence_vector T e) := by
        refine Finset.sum_congr rfl ?_
        intro T hT
        calc
          ((delta i ∩ T).card : ℝ) * lam T = lam T * ((delta i ∩ T).card : ℝ) := by
            rw [mul_comm]
          _ = lam T * ((delta i).sum fun e ↦ one_tree_incidence_vector T e) := by
            rw [sum_incidence_eq_card_inter]
          _ = (delta i).sum (fun e ↦ lam T * one_tree_incidence_vector T e) := by
            rw [← Finset.mul_sum]
      _ = (delta i).sum (fun e ↦ oneTrees.sum fun T ↦ lam T * one_tree_incidence_vector T e) := by
        rw [Finset.sum_comm]
      _ = (delta i).sum x := by
        refine Finset.sum_congr rfl ?_
        intro e he
        exact hReconstruct e
      _ = 2 := hxDegree i hi
  have hObjective :
      (∑ e, c e * x e) = held_karp_dantzig_wolfe_objective c oneTrees lam := by
    -- The reconstructed point preserves the objective after regrouping the witness weights.
    calc
      ∑ e, c e * x e = ∑ e, c e * oneTrees.sum (fun T ↦ lam T * one_tree_incidence_vector T e) := by
        refine Finset.sum_congr rfl ?_
        intro e he
        rw [hReconstruct e]
      _ = ∑ e, oneTrees.sum (fun T ↦ c e * (lam T * one_tree_incidence_vector T e)) := by
        refine Finset.sum_congr rfl ?_
        intro e he
        rw [← Finset.mul_sum]
      _ = oneTrees.sum (fun T ↦ ∑ e, c e * (lam T * one_tree_incidence_vector T e)) := by
        rw [Finset.sum_comm]
      _ = oneTrees.sum (fun T ↦ one_tree_cost c T * lam T) := by
        refine Finset.sum_congr rfl ?_
        intro T hT
        calc
          ∑ e, c e * (lam T * one_tree_incidence_vector T e) =
              ∑ e, (c e * one_tree_incidence_vector T e) * lam T := by
            refine Finset.sum_congr rfl ?_
            intro e he
            ring_nf
          _ = (∑ e, c e * one_tree_incidence_vector T e) * lam T := by
            rw [Finset.sum_mul]
          _ = one_tree_cost c T * lam T := by
            rw [cost_dot_incidence_eq_one_tree_cost]
      _ = held_karp_dantzig_wolfe_objective c oneTrees lam := by
        rfl
  exact ⟨lam, ⟨hLamDegree, hLamSum, hLamNonneg⟩, hObjective⟩

/-- Example 8.12. The Held-Karp Dantzig-Wolfe relaxation over the family of 1-trees has the same
value as the convex-hull one-tree bound with the degree equations `sum_{e in delta(i)} x_e = 2`
for every vertex away from the distinguished root. -/
theorem held_karp_dantzig_wolfe_relaxation_value_eq_one_tree_bound_value
    [Fintype E]
    (root : V)
    (delta : V → Finset E)
    (oneTrees : Finset (Finset E))
    (c : E → ℝ) :
    held_karp_dantzig_wolfe_relaxation_value root delta oneTrees c =
      held_karp_one_tree_bound_value root delta oneTrees c := by
  -- Match the two optimization problems by proving their objective image sets coincide.
  have hImages :
      held_karp_dantzig_wolfe_objective c oneTrees ''
          held_karp_dantzig_wolfe_feasible_set root delta oneTrees =
        (fun x : E → ℝ ↦ ∑ e, c e * x e) ''
          held_karp_one_tree_bound_feasible_set root delta oneTrees := by
    ext y
    constructor
    · rintro ⟨lam, hLam, rfl⟩
      -- Forward transport: feasible master coefficients give a feasible convex-hull point.
      rcases exists_one_tree_bound_point_of_master_feasible root delta oneTrees c lam hLam with
        ⟨x, hx, hObjective⟩
      exact ⟨x, hx, hObjective.symm⟩
    · rintro ⟨x, hx, rfl⟩
      -- Reverse transport: a feasible convex-hull point gives feasible master coefficients.
      rcases exists_master_feasible_of_one_tree_bound_point root delta oneTrees c x hx with
        ⟨lam, hLam, hObjective⟩
      exact ⟨lam, hLam, hObjective.symm⟩
  -- Once the image sets agree, the two infima are definitionally the same.
  exact congrArg sInf <| by
    simpa [held_karp_dantzig_wolfe_relaxation_value, held_karp_one_tree_bound_value] using hImages

end Example812
