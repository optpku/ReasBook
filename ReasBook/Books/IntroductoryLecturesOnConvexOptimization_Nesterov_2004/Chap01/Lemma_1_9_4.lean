/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Gradient
open scoped Topology

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Lemma 1.9.4 lies in the quadratic/Krylov domain.

Sampled owner declarations in this domain:
* `LinearMap.krylovSubspace`, the ambient Krylov-space owner;
* `LinearMap.map_mem_krylovSubspace_succ`, the owner-side image-to-next-stage theorem;
* `problem.krylovSubspace x0 k`, the project-level owner for `𝓛ₖ`;
* `problem.krylovSubspace_eq_span_positiveIterates`, the canonical positive-iterate expansion;
* `problem.affineKrylovSearchSpace x0 k`, the affine owner for `x₀ + 𝓛ₖ`.

Best owner abstraction:
* the pair `problem.krylovSubspace x0 k` / `problem.affineKrylovSearchSpace x0 k`.

Primitive data:
* `problem : UnconstrainedQuadraticMinimizationProblem n`;
* the initial point `x0`;
* the stage `k : ℕ+`;
* a finite family `points : Fin k → E` together with the stagewise minimizing data on
  `x₀ + 𝓛ᵢ`;
* equivalently, the owner datum `IsConjugateGradientSequence problem x0 xs`.

Derived API:
* `problem.gradient_eq`;
* the owner-side bridge
  `gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace`;
* the owner-side orthogonality bridge
  `gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace`;
* the owner-side inclusion companion
  `span_gradients_le_krylovSubspace_of_mem_affineKrylovSearchSpace`;
* the minimizer-based bridge
  `krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers`;
* the source-facing owner theorem
  `IsConjugateGradientSequence.krylovSubspace_eq_span_gradients`.

Source/core/bridge triage:
* source-facing:
  `IsConjugateGradientSequence.krylovSubspace_eq_span_gradients`;
* core/canonical:
  `LinearMap.krylovSubspace`,
  `LinearMap.map_mem_krylovSubspace_succ`,
  `problem.krylovSubspace x0 k`,
  `problem.krylovSubspace_eq_span_positiveIterates`,
  `problem.affineKrylovSearchSpace x0 k`;
* bridge/view:
  the pointwise lemma `gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace`, the
  owner-side orthogonality bridge
  `gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace`, and the inclusion
  companion
  `span_gradients_le_krylovSubspace_of_mem_affineKrylovSearchSpace`, together with the explicit
  minimizing-data bridge
  `krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers`.
-/

namespace UnconstrainedQuadraticMinimizationProblem

/-- Helper for Lemma 1.9.4: a minimizer on an affine subspace has gradient orthogonal to every
vector in the direction of that affine subspace. -/
private theorem inner_gradient_eq_zero_of_mem_direction_of_affineSubspace_minimizer
    {f : E → ℝ} {x : E} {s : AffineSubspace ℝ E}
    (hf : DifferentiableAt ℝ f x) (hx : x ∈ s) (hmin : IsMinOn f (s : Set E) x)
    {v : E} (hv : v ∈ s.direction) :
    inner ℝ (∇ f x) v = 0 := by
  -- Move both `v` and `-v` into the tangent cone using affine-subspace feasibility along rays.
  have hv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (s.direction.smul_mem t hv) hx
  have hv_pos :
      v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hv_eventually.frequently
  have hnegv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (-v) ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction
        (s.direction.smul_mem t (Submodule.neg_mem _ hv)) hx
  have hnegv_pos :
      -v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hnegv_eventually.frequently
  -- First-order optimality on the affine subspace kills the directional derivative.
  have hderiv :
      (fderiv ℝ f x : E →L[ℝ] ℝ) v = 0 := by
    exact
      hmin.localize.hasFDerivWithinAt_eq_zero
        hf.hasFDerivAt.hasFDerivWithinAt hv_pos hnegv_pos
  -- Convert the directional derivative back to the inner-product gradient formula.
  simpa [hf.hasGradientAt.fderiv_apply] using hderiv

private theorem span_range_eq_span_range_init_sup_span_last
    {m : ℕ} (xs : Fin (m + 1) → E) :
    Submodule.span ℝ (Set.range xs) =
      Submodule.span ℝ (Set.range (Fin.init xs)) ⊔ ℝ ∙ xs (Fin.last m) := by
  have hset : Set.range xs = insert (xs (Fin.last m)) (Set.range (Fin.init xs)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.lastCases ?_ ?_ i
      · simp
      · intro j
        right
        exact ⟨j, rfl⟩
    · intro hy
      rcases hy with rfl | ⟨j, rfl⟩
      · exact ⟨Fin.last m, rfl⟩
      · exact ⟨j.castSucc, rfl⟩
  rw [hset, Submodule.span_insert, sup_comm]

private theorem krylovSubspace_succ_eq_of_minimizer_mem_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E) (k : ℕ+)
    (hmin : problem.minimizer ∈ problem.affineKrylovSearchSpace x0 k) :
    problem.krylovSubspace x0 (k + 1) = problem.krylovSubspace x0 k := by
  let A := problem.A.toEuclideanLin
  let seed := ∇ problem.objective x0
  have hx0min : x0 - problem.minimizer ∈ problem.krylovSubspace x0 k := by
    have hsub : problem.minimizer - x0 ∈ problem.krylovSubspace x0 k := by
      simpa using hmin
    simpa using Submodule.neg_mem (problem.krylovSubspace x0 k) hsub
  have hsucc_le_map :
      problem.krylovSubspace x0 (k + 1) ≤ Submodule.map A (problem.krylovSubspace x0 k) := by
    simpa [UnconstrainedQuadraticMinimizationProblem.krylovSubspace, A, seed] using
      LinearMap.krylovSubspace_succ_le_map_of_preimage_mem A k seed (x0 - problem.minimizer)
        hx0min (by simpa [A, seed] using (problem.gradient_eq x0).symm)
  have hAinj : Function.Injective A := by
    intro u v huv
    have hcoords : problem.A.mulVec u.ofLp = problem.A.mulVec v.ofLp := by
      simpa only [A, Matrix.ofLp_toLpLin] using congrArg (fun z : E ↦ z.ofLp) huv
    have hmulVec_inj : Function.Injective problem.A.mulVec :=
      (Matrix.mulVec_injective_iff_isUnit).2 problem.posDef.isUnit
    have huv' : u.ofLp = v.ofLp := hmulVec_inj hcoords
    exact congrArg (WithLp.toLp 2) huv'
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo A hAinj
  have hmap_finrank :
      Module.finrank ℝ ↥(Submodule.map A (problem.krylovSubspace x0 k)) =
        Module.finrank ℝ ↥(problem.krylovSubspace x0 k) := by
    have h := LinearEquiv.finrank_map_eq e (problem.krylovSubspace x0 k)
    simpa [e] using h
  have hL_le_map :
      problem.krylovSubspace x0 k ≤ Submodule.map A (problem.krylovSubspace x0 k) := by
    exact le_trans
      (problem.krylovSubspace_mono x0
        (show (k : ℕ) ≤ ((k + 1 : ℕ+) : ℕ) by exact Nat.le_succ _))
      hsucc_le_map
  have hL_eq_map :
      problem.krylovSubspace x0 k = Submodule.map A (problem.krylovSubspace x0 k) := by
    exact Submodule.eq_of_le_of_finrank_eq hL_le_map hmap_finrank.symm
  apply le_antisymm
  · rw [← hL_eq_map] at hsucc_le_map
    exact hsucc_le_map
  · exact problem.krylovSubspace_mono x0
      (show (k : ℕ) ≤ ((k + 1 : ℕ+) : ℕ) by exact Nat.le_succ _)

/-- If `x` minimizes the quadratic objective on `x₀ + 𝓛ₖ`, then the gradient at `x` is orthogonal
to `𝓛ₖ`. -/
theorem gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 x : E) (k : ℕ+)
    (hx : x ∈ problem.affineKrylovSearchSpace x0 k)
    (hmin : IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 k : Set E) x) :
    ∇ problem.objective x ∈ (𝓛(problem, x0, k))ᗮ := by
  -- The quadratic objective is differentiable, so first-order optimality on the affine space
  -- turns every search direction into an orthogonality relation with the gradient.
  have hdiff : DifferentiableAt ℝ problem.objective x := by
    have hsymm : problem.A.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
    simpa [UnconstrainedQuadraticMinimizationProblem.objective] using
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        problem.α problem.a problem.A hsymm).1.differentiable_one x
  rw [Submodule.mem_orthogonal']
  intro v hv
  exact
    inner_gradient_eq_zero_of_mem_direction_of_affineSubspace_minimizer
      hdiff hx hmin (by
        simpa [UnconstrainedQuadraticMinimizationProblem.affineKrylovSearchSpace] using hv)

/-- If `x ∈ x0 + 𝓛ₖ`, then the gradient at `x` lies in the next Krylov stage `𝓛ₖ₊₁`. -/
-- Proof sketch: write `x = x0 + v` with `v ∈ 𝓛ₖ`. The gradient formula `problem.gradient_eq`
-- identifies `∇ problem.objective x` with the seed `A (x0 - x*)` plus the image `A v`. The first
-- term lies in the first Krylov stage, and the second term is sent into the next stage by the
-- owner-side theorem `LinearMap.map_mem_krylovSubspace_succ`.
theorem gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 x : E) (k : ℕ+)
    (hx : x ∈ problem.affineKrylovSearchSpace x0 k) :
    ∇ problem.objective x ∈ 𝓛(problem, x0, k + 1) := by
  let A := problem.A.toEuclideanLin
  let seed := ∇ problem.objective x0
  have hx' : x - x0 ∈ 𝓛(problem, x0, k) := by
    simpa using hx
  have hxA : x - x0 ∈ A.krylovSubspace k seed := by
    simpa [krylovSubspace, A, seed] using hx'
  have hseed : seed ∈ A.krylovSubspace (k + 1) seed := by
    rw [LinearMap.krylovSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hmap : A (x - x0) ∈ A.krylovSubspace (k + 1) seed := by
    simpa [A, seed] using LinearMap.map_mem_krylovSubspace_succ A seed hxA
  rw [problem.gradient_eq]
  have hsplit :
      A (x - problem.minimizer) = seed + A (x - x0) := by
    calc
      A (x - problem.minimizer)
          = A ((x0 - problem.minimizer) + (x - x0)) := by
              congr 1
              abel
      _ = A (x0 - problem.minimizer) + A (x - x0) := by simp
      _ = seed + A (x - x0) := by
            rw [show A (x0 - problem.minimizer) = seed by
              simpa [A, seed] using (problem.gradient_eq x0).symm]
  rw [hsplit]
  change seed + A (x - x0) ∈ A.krylovSubspace (k + 1) seed
  exact Submodule.add_mem _ hseed hmap

/-- Under the affine-membership hypotheses, the span of the gradients at
`x₀, x₁, …, xₖ₋₁` lies in the `k`th Krylov space `𝓛ₖ`. This owner-side inclusion is the
companion bridge used by later chapter arguments. -/
-- Proof sketch: the base point contributes `∇ problem.objective x0`, which is the first Krylov
-- generator. For `i > 0`, the hypothesis `xᵢ ∈ x₀ + 𝓛ᵢ` and the pointwise bridge above show that
-- `∇ problem.objective (xᵢ)` lies in `𝓛ᵢ₊₁`; owner-side monotonicity
-- `problem.krylovSubspace_mono x0` then moves this into `𝓛ₖ`, so every spanning gradient belongs
-- to `𝓛ₖ`.
theorem span_gradients_le_krylovSubspace_of_mem_affineKrylovSearchSpace
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E)
    (k : ℕ+) (points : Fin k → E)
    (hx0 : points 0 = x0)
    (hpoints :
      ∀ i : Fin k, ∀ hi : 0 < i,
        points i ∈ problem.affineKrylovSearchSpace x0 ⟨i, hi⟩) :
    Submodule.span ℝ
      (Set.range fun i : Fin k ↦
        ∇ problem.objective (points i)) ≤
      𝓛(problem, x0, k) := by
  let A := problem.A.toEuclideanLin
  let seed := ∇ problem.objective x0
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rcases eq_or_ne i 0 with rfl | hi
  · have hseed : seed ∈ A.krylovSubspace k seed := by
      rw [LinearMap.krylovSubspace]
      exact Submodule.subset_span ⟨0, by simp⟩
    change ∇ problem.objective (points 0) ∈ A.krylovSubspace k seed
    rw [hx0]
    simpa [seed] using hseed
  · have hi0 : 0 < i := Fin.pos_iff_ne_zero.2 hi
    have hgrad :
        ∇ problem.objective (points i) ∈ 𝓛(problem, x0, Nat.succPNat i) := by
      simpa using
        gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace
          problem x0 (points i) ⟨i, hi0⟩ (hpoints i hi0)
    have hmono :
        𝓛(problem, x0, Nat.succPNat i) ≤ 𝓛(problem, x0, k) := by
      exact problem.krylovSubspace_mono x0 (Nat.succ_le_of_lt i.is_lt)
    exact hmono hgrad

/-- Bridge form of Lemma 1.9.4: if each `xᵢ` with `0 < i < k` lies in and minimizes the quadratic
objective on the affine Krylov search space `x₀ + 𝓛ᵢ`, then `𝓛ₖ` is exactly the span of the
gradients at `x₀, x₁, …, xₖ₋₁`. This is the explicit minimizing-data version of the conjugate-
gradient statement. -/
theorem
    krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x0 : E)
    (k : ℕ+) (points : Fin k → E)
    (hx0 : points 0 = x0)
    (hpoints :
      ∀ i : Fin k, ∀ hi : 0 < i,
        points i ∈ problem.affineKrylovSearchSpace x0 ⟨i, hi⟩)
    (hmins :
      ∀ i : Fin k, ∀ hi : 0 < i,
        IsMinOn problem.objective
          (problem.affineKrylovSearchSpace x0 ⟨i, hi⟩ : Set E)
          (points i)) :
    𝓛(problem, x0, k) =
      Submodule.span ℝ
        (Set.range fun i : Fin k ↦
          ∇ problem.objective (points i)) := by
  induction k using PNat.recOn with
  | one =>
      have hleft :
          Set.range (fun i : Fin 1 ↦
            (problem.A.toEuclideanLin ^ (i : ℕ)) (∇ problem.objective x0)) =
            {∇ problem.objective x0} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          simp
        · rintro rfl
          exact ⟨0, by simp⟩
      have hrange :
          Set.range (fun i : Fin 1 ↦ ∇ problem.objective (points i)) =
            {∇ problem.objective x0} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          simpa using congrArg (fun z ↦ ∇ problem.objective z) hx0
        · rintro rfl
          exact ⟨0, by simpa using congrArg (fun z ↦ ∇ problem.objective z) hx0⟩
      rw [UnconstrainedQuadraticMinimizationProblem.krylovSubspace, LinearMap.krylovSubspace]
      simp [hrange]
  | succ k hk =>
      have hprefix :
          𝓛(problem, x0, k) =
            Submodule.span ℝ
              (Set.range fun i : Fin k ↦
                ∇ problem.objective ((Fin.init points) i)) := by
        refine hk (Fin.init points) ?_ ?_ ?_
        · simpa using hx0
        · intro i hi
          simpa using hpoints i.castSucc hi
        · intro i hi
          simpa using hmins i.castSucc hi
      let glast := ∇ problem.objective (points (Fin.last k))
      have hspan :
          Submodule.span ℝ
            (Set.range fun i : Fin (k + 1) ↦
              ∇ problem.objective (points i)) =
              Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) ⊔
                ℝ ∙ glast := by
        simpa [glast, Fin.init] using
          span_range_eq_span_range_init_sup_span_last
            (fun i : Fin ((k + 1 : ℕ+) : ℕ) ↦
              ∇ problem.objective (points i))
      have hlast_pos : 0 < Fin.last k := Fin.pos_iff_ne_zero.mpr (by simp)
      have hlast_mem :
          points (Fin.last k) ∈ problem.affineKrylovSearchSpace x0 k := by
        simpa using hpoints (Fin.last k) hlast_pos
      have hlast_min :
          IsMinOn problem.objective
            (problem.affineKrylovSearchSpace x0 k : Set E)
            (points (Fin.last k)) := by
        simpa using hmins (Fin.last k) hlast_pos
      by_cases hzero : glast = 0
      · have hlast_eq_min : points (Fin.last k) = problem.minimizer := by
          exact problem.eq_minimizer_of_gradient_eq_zero hzero
        have hmin_mem :
            problem.minimizer ∈ problem.affineKrylovSearchSpace x0 k := by
          simpa [hlast_eq_min] using hlast_mem
        calc
          𝓛(problem, x0, k + 1) = 𝓛(problem, x0, k) := by
                  exact
                    krylovSubspace_succ_eq_of_minimizer_mem_affineKrylovSearchSpace
                      problem x0 k hmin_mem
          _ = Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) := hprefix
          _ = Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) ⊔
                ℝ ∙ glast := by simp [hzero]
          _ = Submodule.span ℝ
                (Set.range fun i : Fin (k + 1) ↦
                  ∇ problem.objective (points i)) := hspan.symm
      · have hgrad_mem :
            glast ∈ 𝓛(problem, x0, k + 1) := by
          simpa [glast] using
            gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSearchSpace
              problem x0 (points (Fin.last k)) k hlast_mem
        have hgrad_orth :
            glast ∈ (𝓛(problem, x0, k))ᗮ := by
          simpa [glast] using
            gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace
              problem x0 (points (Fin.last k)) k hlast_mem hlast_min
        have hgrad_not_mem : glast ∉ 𝓛(problem, x0, k) := by
          intro hgk
          have hself : inner ℝ glast glast = 0 :=
            (Submodule.mem_orthogonal' _ _).1 hgrad_orth glast hgk
          exact hzero (inner_self_eq_zero.mp hself)
        have hsup_le :
            𝓛(problem, x0, k) ⊔ ℝ ∙ glast ≤ 𝓛(problem, x0, k + 1) := by
          refine sup_le ?_ ?_
          · exact problem.krylovSubspace_mono x0
              (show (k : ℕ) ≤ (((k + 1 : ℕ+) : ℕ)) by exact Nat.le_succ _)
          · exact (Submodule.span_singleton_le_iff_mem _ _).2 hgrad_mem
        have hfin_le :
            Module.finrank ℝ ↥(𝓛(problem, x0, k + 1)) ≤
              Module.finrank ℝ ↥(𝓛(problem, x0, k)) + 1 := by
          simpa [UnconstrainedQuadraticMinimizationProblem.krylovSubspace] using
            LinearMap.finrank_krylovSubspace_succ_le
              problem.A.toEuclideanLin k (∇ problem.objective x0)
        have hsup_finrank :
            Module.finrank ℝ ↥(𝓛(problem, x0, k) ⊔ ℝ ∙ glast) =
              Module.finrank ℝ ↥(𝓛(problem, x0, k)) + 1 := by
          exact Submodule.finrank_sup_span_singleton hgrad_not_mem
        have hfin_eq :
            Module.finrank ℝ ↥(𝓛(problem, x0, k) ⊔ ℝ ∙ glast) =
              Module.finrank ℝ ↥(𝓛(problem, x0, k + 1)) := by
          apply le_antisymm
          · exact Submodule.finrank_mono hsup_le
          · calc
              Module.finrank ℝ ↥(𝓛(problem, x0, k + 1))
                  ≤ Module.finrank ℝ ↥(𝓛(problem, x0, k)) + 1 := hfin_le
              _ = Module.finrank ℝ ↥(𝓛(problem, x0, k) ⊔ ℝ ∙ glast) := by
                    rw [hsup_finrank]
        have hsup_eq :
            𝓛(problem, x0, k) ⊔ ℝ ∙ glast =
              𝓛(problem, x0, k + 1) := by
          exact Submodule.eq_of_le_of_finrank_eq hsup_le hfin_eq
        calc
          𝓛(problem, x0, k + 1) = 𝓛(problem, x0, k) ⊔ ℝ ∙ glast := hsup_eq.symm
          _ = Submodule.span ℝ
                (Set.range fun i : Fin k ↦
                  ∇ problem.objective ((Fin.init points) i)) ⊔
                ℝ ∙ glast := by rw [hprefix]
          _ = Submodule.span ℝ
                (Set.range fun i : Fin (k + 1) ↦
                  ∇ problem.objective (points i)) := hspan.symm

/-- Lemma 1.9.4: along a conjugate-gradient sequence, the `k`th Krylov space `𝓛ₖ` is exactly the
span of the gradients at the first `k` trajectory points `x₀, x₁, …, xₖ₋₁`. Equivalently, the
nonzero gradients/residuals generated by the minimizing Krylov process span `𝓛ₖ`. -/
theorem IsConjugateGradientSequence.krylovSubspace_eq_span_gradients
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    𝓛(problem, x0, k) =
      Submodule.span ℝ
        (Set.range fun i : Fin k ↦
          ∇ problem.objective (conjugateGradientTrajectory x0 xs i)) := by
  refine
    krylovSubspace_eq_span_gradients_of_affineKrylovMinimizers problem
      x0 k (fun i : Fin k ↦ conjugateGradientTrajectory x0 xs i) ?_ ?_ ?_
  · simp
  · intro i hi
    rcases i with ⟨i, hik⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    simpa [conjugateGradientTrajectory] using hcg.mem_affineKrylovSearchSpace j.succPNat
  · intro i hi
    rcases i with ⟨i, hik⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    simpa [conjugateGradientTrajectory] using hcg.isMinOn_affineKrylovSearchSpace j.succPNat

end UnconstrainedQuadraticMinimizationProblem
